## What changed

The unchanged declaration `AlgebraicGeometry.Scheme.finiteEtale_adic_sections_kernel`
now has a complete Lean proof from two strictly smaller geometric statements. Its
signature, universe, public imports and original docstring are unchanged.

The proof takes the finite locally free direct image of the structure sheaf, embeds
it in finite free with locally free cokernel, and embeds that cokernel in another
finite free sheaf. Their composite defines the relation matrix. The proof of the
kernel lifting assertion uses the abelian image/kernel isomorphism and sections
preserving kernels; it does not assume that sections preserve cokernels.

Canonical base-change maps are constructed in the new module
`Sheaf.AlgebraicGeometry.Morphisms.FiniteEtaleAdicPushforwardCoordinates` by the
pullback/pushforward adjunction applied to restriction of functions. The section
lift is `Function.invFun` of this concrete map, and coordinates apply the pulled-back
embedding and the canonical finite free coordinate equivalence. No data is taken
from an arbitrary witness of a holed existence theorem. Bijectivity of this map is
proved in the item's module using the existing affine base-change theorem, uniqueness
of left adjoints, and the tensor pullback of the structure sheaf. The projection
formula is also proved by adjunction-unit naturality. Only transition naturality is
left as a new theorem.

The other new module is
`Sheaf.AlgebraicGeometry.Modules.QuasiAffineLocallyFreeEmbedding`, whose theorem
provides one universally monic finite free embedding with locally free cokernel.
It is used twice. All new proof imports in the item are non-public. There are no
changes or forced adaptations of other existing modules. The parent node's proof,
proof dependencies and proof origin are updated to describe this actual route.

## Proved and sorry left

Closed the one original hole:
`AlgebraicGeometry.Scheme.finiteEtale_adic_sections_kernel`
(`new-finite-etale-adic-sections-kernel`). The item's module has no sorry left.

Added two named public theorem holes, each in its own new module:

- `AlgebraicGeometry.Scheme.Modules.exists_universally_mono_free`
  (`new-sbc-quasi-affine-locally-free-embedding`). This is one sheaf embedding on a
  Noetherian quasi-affine open; it has no adic parameter, section-kernel conclusion,
  matrix, or comparison assertion.
- `AlgebraicGeometry.Scheme.FiniteEtale.Adic.pushforward_coordinates_transition`
  (`new-sbc-finite-etale-adic-pushforward-coordinates`). This proves only the transition
  formula for the explicitly constructed coordinates and an arbitrary morphism into
  finite free. It does not assert an embedding, injectivity, kernel lifting, matrix
  relations, or projection compatibility, and does not assume Noetherianity.

Thus this is a decomposition: one upper hole closed, two lower holes added. It is
not a proof free of sorry in its transitive dependency closure. Existing finite
pushforward, affine base-change and tensor structure-sheaf declarations are used
with their original statements.

All six conjuncts of the item are combined by real Lean proofs: both injectivity
assertions, kernel lifting, pulled-back matrix relations, projection compatibility,
and transition compatibility. The private helpers for evaluation of monomorphisms,
kernel lifting, canonical comparison bijectivity, the adjunction unit, free coordinate
pullback and matrix pullback have complete proofs.

Validation: all three modules compile together through `lcompile.py --all`, with
no warnings. The empty open and ranks zero are covered by the same constructions;
no nonempty or constant-rank hypotheses enter the new statements. For the embedding,
a local split inclusion survives arbitrary non-flat pullback; the cokernel is finite
locally free because a finite projective summand is locally free. For the transition
statement, zero coordinates and empty schemes give the same functorial identities.

## No longer needed

None of the original imports or original planned proof dependencies is removed.
`lem-pc-finite-flat-pushforward-locally-free` remains necessary. The unit's realized
records are unchanged, and no unit route is bypassed. No additional planned node or
module is claimed pruned.

No separate new theorem is needed for global-section kernel exactness, preservation
of monomorphisms on sections, matrix pullback, canonical comparison bijectivity,
or projection compatibility: all are proved in the item from existing declarations.
The second new theorem was narrowed during implementation to transition compatibility.

## Where the brief, the DAG or earlier work was wrong

The old parent plan correctly identified the geometric argument, but did not name
Lean statements for its finite free embedding or its canonical transition naturality.
The existing finite pushforward dependency alone does not provide these. Those two
missing parts are now explicit nodes with Lean statements and complete proofs in words.
Affine base-change bijectivity and projection compatibility did not require new holes.

The original parent's `blueprint.from.node` points to the created transfer node rather
than the imported blueprint ancestor. The ancestor tool consequently reports no
nearest blueprint ancestor for the parent. The new nodes record the actual ancestor
`sbc-thm-spreading-finite-etale-galois`, reached through the parent, transfer and the
three comparison/algebraization nodes listed in their `via` fields. The parent's
blueprint metadata is not edited, because it is outside a stage-3 worker's fields.

LeanSearch returned Internal Server Error for both semantic queries. Loogle did not
recognize the finite locally free identifier. These are recorded as unavailable,
not as evidence of an absent theorem. LeanFinder, Mathlib source grep and library/DAG
search found no exact existing statement for either remaining geometric lemma.

## New nodes

`new-sbc-quasi-affine-locally-free-embedding`, in
`dag/nodes/sec-smooth-base-change/`, states the first dual-surjection construction of
Stacks Tag 0EKP. Its proof explains global generation by extending basis sections
from finitely many principal affine opens using the existing denominator-clearing
lemma, then local splitting, dualization, and arbitrary-pullback preservation.
It is realized by `Sheaf.AlgebraicGeometry.Modules.QuasiAffineLocallyFreeEmbedding`.

`new-sbc-finite-etale-adic-pushforward-coordinates`, in the same chapter, states only
the consecutive-thickening coordinate formula. Its canonical maps and inverse are
concrete definitions. The proof explains pullback pasting, affine tensor base change,
associativity on pure tensors, passage to unique inverses, and naturality of finite
free projections. Its sources are Stacks Tags 02KG and 0EKP. It is realized by
`Sheaf.AlgebraicGeometry.Morphisms.FiniteEtaleAdicPushforwardCoordinates`.

Both inherit the parent's chapter and unit, contain the three required kinds of
Mathlib search, and cite the actual blueprint ancestor. No change record is needed:
no existing statement, definition or interface changes.

## Second reading by R4

1. Interface: PASS. Read the diff against the repository and compared the declaration
   tables. The original theorem's statement, docstring, visibility and universe are
   unchanged. Its two public imports remain unchanged. Every added import in the item
   is a proof import. No existing definition or other module is adapted, and no change
   record is required.
2. Proof and construction: PASS as a decomposition, not a closed axiom-free proof.
   All three delivered files compile together through the prescribed `lcompile.py`.
   There are exactly the two reported whole-proof sorries in named public theorems;
   the item has none. A scratch-copy `#print axioms` check found only propext,
   Classical.choice, Quot.sound and sorryAx for the item and the two open theorems.
   The four new definitions coverToBase, pushforwardComparison, liftSection and
   coordinates use only the three allowed axioms, without sorryAx. In particular,
   liftSection inverts a concretely constructed map; it does not choose an arbitrary
   witness of an unproved existence theorem. The proof's choice of a tensor-pullback
   adjunction is legitimate: the adjunction on the fixed functors is unique.
   Kernel lifting uses preservation of kernels and the abelian image isomorphism,
   not surjectivity of global sections of a sheaf epimorphism.
3. Split statements: PASS. Read both Lean statements, full docstring arguments and
   node records. The embedding is the dual of a finite generating surjection onto
   the dual bundle; its locally split cokernel is finite locally free, so arbitrary
   pullback preserves monicity. Noetherianity ensures the open has a finite cover.
   Empty opens, the zero ring, zero bundles and varying ranks cause no exception.
   The transition assertion is naturality of the canonical affine comparison and
   finite free projections. Its inverse is well-defined because the comparison is
   invertible for finite morphisms; empty schemes and r = 0 cause no exception.
   Neither statement restates the item's six-conjunct conclusion. Independent
   LeanFinder searches used “direct summand” and “composition of base morphisms”;
   Mathlib grep used “globally generated” and “base change composition”, and source
   rg searched embeddings, dual surjections and universal monicity. No exact
   existing theorem was found. The existing pushforwardComp and pullback-unit
   composition lemmas provide ingredients, not either complete missing assertion.
   Neither remaining geometric proof can be closed by a short application of the
   search results.
4. Route and pruning: PASS. Read the proof from the item down to its helpers and
   dependencies. The two embeddings, section-kernel lifting, matrix pullback,
   comparison bijectivity and projection identity are actual reductions. The added
   imports supply the two split statements, affine base change, the tensor unit
   comparison, pullback on sections and quasicoherence of the unit. The sole old
   planned dependency, finite-flat pushforward local freeness, remains used, so
   “No longer needed” is complete. The unit sk-prop-input-spreading has empty
   realized arrays in the repository; these existing arrays are unchanged, and
   this reduction is below its geometric spreading argument.
5. DAG: PASS. The existing node changes only proof, proof_deps and proof_origin.
   Each new node has matching Lean text, source, complete argument, search records,
   creation record, chapter/unit and blueprint ancestry. Each proof_deps set is
   exactly the union of its steps' uses. Checked the cited sources directly:
   [Stacks 0EKP](https://stacks.math.columbia.edu/tag/0EKP) supplies the dual-surjection
   route, and [Stacks 02KG](https://stacks.math.columbia.edu/tag/02KG) supplies affine
   quasi-coherent base change. Their arguments support these specializations.

Changed in the second reading: this report only. No mathematical or Lean repair was
needed. One original hole is closed and two strictly smaller holes are added; no
module is claimed pruned and no net decrease of holes is claimed.
