## What changed

Replaced the single sorry in
`WeilConjectures.AlgebraicGeometry.Sites.AffineTorsionCohomologicalDimension` by a
compiling proof from the new affine-line projection stalk lemma and existing library
results. The public theorem and its three public imports are unchanged. All new
proof imports are private imports.

The proof performs strong induction on dimension over all algebraically closed
fields simultaneously. Finite pushforward, Noether normalization, affine
identification with Spec, and algebraic-closure descent reduce the assertion to
polynomial rings. The induction supplies punctured strict-local bounds via the
smooth coefficient-field model, a rational-function coefficient field, transcendence
degree, and filtered finitely generated subalgebras. A directed system of kernels
supported on closed complements reduces support-dimension vanishing to the smaller
affine cases. Leray diagonal vanishing then proves the affine-space bound.

The last-coordinate polynomial projection is explicitly identified with the
structural morphism of a relative affine line: rotate the coordinates, use the
polynomial-ring equivalences, take Spec, and verify the base map. This is supplied
to the remaining geometric lemma.

The projective-line direct-image bound is proved from the existing projective-line
geometric-stalk comparison and the curve bound. An equivalence with sheaves of
modules over a universe lift of the integers and exact derived-composition
comparisons transfer it to abelian sheaves. The proof also supplies closed-section
acyclicity, vanishing of positive open-immersion direct images on the open,
and the resulting mixed-degree boundary acyclicity. It also supplies the ordinary
right-derived form of the strict-local stalk formula and Leray diagonal vanishing
after exact inverse image.
Thus the remaining geometric lemma receives those five facts as proved inputs.

To keep compilation within the per-file budget, the closed-complement subscheme
the coefficient-equivalence preimage, and the comparison isomorphisms are
abstracted through existential elimination. Kernel inclusions use their explicit maps, and evaluation additivity
is proved directly by its `map_add` field. The kernel-inclusion Mono fact is a
private theorem installed only as a local instance where the filtration uses it;
no global instance is added.

Added `Sheaf.AlgebraicGeometry.Sites.AffineLineProjectionStalkBound` and its node.
Updated the original blueprint node's proof, proof dependencies, and proof origin to
record the route actually implemented. Its existing Lean attachment is retained:
it names the separate Sheaf wrapper, which this delivery does not change.

## Proved and sorry left

Closed the original hole in
`AlgebraicGeometry.Scheme.hasTorsionCohomologicalDimensionLE_of_isAffine`.
Its proof and every private helper in the assigned module are complete. In
particular, the following substantial parts are proved in the assigned module:
`support_dimension_H`, `torsionCd_principalOpen_of_trdeg`,
`strictLocal_principalOpen_bound`, `projectiveLine_rightDerived_isZero`,
`rightDerived_openImmersion_boundary_acyclic`,
`isZero_stalk_rightDerived_of_strictLocal_H`,
`isZero_pullback_rightDerived_comp_of_diagonal`, and
`exists_affineSpace_line_iso`.

Added one hole:
`AlgebraicGeometry.Scheme.affineLineProjection_stalk_bound`
(node `lem-sc-affine-line-projection-stalk-bound`). This is a decomposition, with
one original hole closed and one new hole added, not an axiom-free proof of the
whole affine theorem. Existing imported theorems that contain sorry remain existing
obligations; none is restated under a new name in this delivery.

The new hole is strictly the compactification-and-stalk part of the argument. It
asserts vanishing at individual points for positive higher direct images of one
explicit affine-space projection. It does not assert any global affine
cohomological-dimension bound. The caller proves the projective-line bound,
closed-section acyclicity, strict-local comparison, and punctured-local induction
hypothesis supplied to it. What remains is to compose the proved relative-affine-line
identification with the standard projective-line chart, identify the infinity
strict-local complement, apply Leray diagonal vanishing above degree two, and treat
degree two at the generic point of the base. Its docstring gives these steps and
the separably closed field descent explicitly.

Both sandbox modules compile together using `lcompile.py --all`; the assigned
module has no remaining sorry and the new module has exactly its one named sorry.

## No longer needed

No original import was removed: the source module originally had only its three
public statement imports, all retained. The following planned dependencies are
omitted from this proof route; this is local pruning, not a claim that their
modules are unused by every other target:

- `cor-weil-pbc-geometric-fiber-finite`, module
  `Sheaf.AlgebraicGeometry.GeometricFiberFinite`: full proper base change is
  unnecessary here. The projective-line geometric-stalk comparison suffices.
- `lem-weil-pbc-exchange-forget-coefficients`, module
  `Sheaf.AlgebraicGeometry.ExchangeForgetCoefficients`: the finite-coefficient
  exchange bridge is replaced here by the equivalence with integer-module sheaves
  and exact ordinary-derived-functor comparison isomorphisms.
- `def-nagata-effective-cartier-ideal`, module
  `WeilConjectures.Mathlib.AlgebraicGeometry.IdealSheaf.Invertible`: the remaining
  compactification argument only needs the explicit infinity-chart coordinate,
  rather than a general invertible-ideal formalism.

The support-union and Grothendieck spectral-sequence wrappers are not imported:
the existing source-library APIs and proved glue implement those same steps.
Their mathematical nodes remain dependencies; this is not pruning those steps.
Removed redundant proof imports introduced while developing the proof; each is
already a public transitive import of a retained module:

- `Mathlib.AlgebraicGeometry.Morphisms.ClosedImmersion`
- `WeilConjectures.AlgebraicGeometry.Sites.SupportDimension`
- `WeilConjectures.AlgebraicGeometry.Sites.CohomologyClopen`
- `WeilConjectures.Mathlib.AlgebraicGeometry.Morphisms.FiniteType`
- `WeilConjectures.Mathlib.RingTheory.NoetherNormalization`
- `Mathlib.CategoryTheory.Limits.Shapes.ConcreteCategory`
- `WeilConjectures.Mathlib.Algebra.Category.Ring.FilteredColimits`
- `Mathlib.RingTheory.LocalRing.ResidueField.Basic`
- `Mathlib.RingTheory.Localization.Away.Basic`
- `Mathlib.Algebra.Polynomial.Div`
- `WeilConjectures.Mathlib.CategoryTheory.Sites.Point.Skyscraper`
- `WeilConjectures.CategoryTheory.DerivedCategory.RightDerivedFunctor.PlusCompatibility`
- `WeilConjectures.CategoryTheory.DerivedCategory.RightDerivedFunctor.PlusSingle`

No existing Lean module is withdrawn.

For completeness, six further entries of the old `proof_deps` are absent from the
calling node's new direct dependency list because the new local geometric node
carries them: `def-sc-etale-torsion-cd`, `def-weil-pbc-inverse-image`,
`sbc-lem-affine-space-smooth`, `def-weil-regular-scheme`,
`lemma-nagata-projective-space-base-change-proper`, and
`lem-weil-pbc-finite-type-domain-dimension-trdeg`. These are dependency moves,
not mathematical steps pruned from the argument.

The second reader also removed redundant direct imports of
`Mathlib.Logic.Equiv.Fin.Rotate` from the assigned module and
`Mathlib.FieldTheory.IsAlgClosed.Basic`,
`Mathlib.AlgebraicGeometry.Morphisms.Smooth`,
`Mathlib.RingTheory.LocalRing.ResidueField.Basic`, and
`Mathlib.RingTheory.Localization.Away.Basic` from the new module. All are public
transitive imports of retained modules. No module leaves the import closure as a
result of removing these redundant edges.

## Where the brief, the DAG or earlier work was wrong

The assigned source module has a blueprint reference to
`thm-sc-affine-torsion-cd`, but the node's Lean attachment names the distinct
`Sheaf.AlgebraicGeometry.Sites.AffineTorsionCohomologicalDimensionOfAffine`
wrapper. That wrapper is unchanged and is not claimed proved here.

Importing the full geometric-fibre proper-base-change statement here would create
an import cycle through proper base change, torsion direct-image vanishing, and
the affine cohomological-dimension theorem. The atomic projective-line
geometric-stalk comparison is acyclic and supplies exactly the case used here.

The support filtration requires genuine closed-complement kernel objects and
transition maps, rather than a bare assertion that support is the union of finite
subsupports. These are constructed explicitly. The empty ring and dimensions zero
and one are treated separately before dimension induction.

## New nodes

`lem-sc-affine-line-projection-stalk-bound` is the remaining local geometric
argument, in
`lean/Sheaf/AlgebraicGeometry/Sites/AffineLineProjectionStalkBound.lean`.
Its proof is the compactification part of `thm-sc-affine-torsion-cd`, with the
strict-local, projective-line, and boundary-section inputs exposed and supplied by
proved helpers in the caller. Its node records the exact Lean statement, source,
complete proof plan, and three kinds of Mathlib search. LeanSearch returned an
internal server error; that unavailable request is recorded without a verdict,
while LeanFinder, Loogle, and source grep were available. No existing public
statement or definition changes, and no forced adaptations or change records are
needed.

## Second reading by P1

1. **Interface preservation: pass.** Compared both delivered modules with the
   shared repository. The new Sheaf module does not exist there. The original
   theorem's signature, including implicit parameters, both typeclass hypotheses,
   structural morphism and dimension inequality, is byte-for-byte unchanged up to
   `:=`; its docstring and three public imports are also unchanged. Every added
   import in the original module is private. No existing definition or statement
   changes, adaptations, or change records are needed.

2. **Proof and data: pass as a decomposition.** Read the entire assigned
   module and the new local lemma. The finite-pushforward torsion argument uses
   finite products, the zero ring is handled separately, and simultaneous strong
   induction really supplies the lower-dimensional bound over `RatFunc F`.
   The support diagram uses actual kernel inclusions and a locally-surjective
   colimit, and the coefficient transfer uses the integer-module equivalence.
   The two new private definitions are explicit constructions: a kernel lift and
   a composite of polynomial ring equivalences. Existential elimination inside
   proofs does not introduce a definition choosing arbitrary unproved data.
   The identity-functor vanishing now uses the existing proved
   `Functor.isZero_rightDerived_obj_of_exact`; its positive-degree hypothesis is
   converted to a successor index. The final induction specializes the local
   projection theorem directly, eliminating an unused higher-order parameter.
   The coordinate equivalence is existentially abstracted within a proof from
   its explicit construction and base-map identity.
   The original module has no `sorry`; the new module has exactly the reported
   named theorem with `:= by sorry`. No forbidden axiom or implementation feature
   occurs. Local compilation and the delivery's all-declaration axiom probe pass;
   `sorryAx` remains permitted only because of imported open statements, including
   the explicitly reported local lemma. This is one hole closed and one added,
   net zero, rather than an axiom-free proof of the affine theorem.

3. **Split statement: pass.** Matched all six supplied inputs and the conclusion
   against the new node's verbatim Lean signature. The conclusion concerns one
   polynomial projection and pointwise higher direct images, strictly a part of
   the original global theorem. Its uniform annihilator is positive; it asserts
   nothing in degrees zero and one. For `n = 0` and `q = 2`, the strict inequality
   forces the generic point of the one-dimensional base, where the affine-curve
   bound gives degree-two vanishing. For `q > n + 2`, the inequality holds at
   every point and the same compactification argument applies. The zero sheaf
   causes no exception. At infinity the boundary coordinate is a nonzerodivisor
   and lies in the strict-local maximal ideal. The strict-local bound used there
   is exactly `d - a`, with `a < d`; the separably closed geometric field is
   handled by purely inseparable algebraic-closure descent. Read the full
   natural-language proof and the original node's twelve-step plan, also
   reproduced in the existing Sheaf wrapper's docstring. The separate cited
   blueprint document is not installed in this checkout.
   Independent searches used LeanFinder with "supported in codimension at least
   the cohomological degree minus one", Loogle with `"rightDerived", "IsZero"`,
   msearch grep with `cohomological.*(codimension|support)|stalk.*(transcendence|trdeg)`,
   and source `rg` on both Lean roots. No matching projection-stalk theorem was
   found; Loogle's injective-object vanishing is insufficient. Blueprint searches
   for "affine line" and "stalk bound" found no duplicate; the constant-coefficient
   purity and Fourier-transform statements do not cover arbitrary bounded-torsion
   sheaves. Closing the remaining compactification theorem requires substantial
   chart and strict-local comparisons, beyond a few-minute repair.

4. **Route and pruning: pass after repair.** The proof follows finite normalization,
   ground-field descent, the rational-function strict-local reduction, projective
   compactification, support filtration, and Leray. No alternative bypass of the
   compact-support base-change unit is introduced. Read
   `dag/units/sk-prop-sf-cbc.json`: its realized statement and step lists are empty,
   and this affine bound is a supporting node, not that unit's key statement;
   the delivery changes no unit record. Removed five redundant imports supplied
   transitively. Replaced the identity-resolution calculation by the existing
   proved exact-functor vanishing theorem, and made local proof
   reductions to avoid repeated elaboration and unfolding. The finite transfer
   now uses the edge map's surjectivity directly. Module-stalk zero is transported
   by its isomorphism, and the exact derived-square calculation is performed once
   for abstract abelian categories rather than with expanded sheaf functors. Completed
   `## No longer needed` with every old proof dependency absent from the new
   calling-node list, distinguishing six moved dependencies from the three
   omitted dependencies. No whole-library module-pruning claim is made.

5. **DAG agreement: pass after repair.** The original node changes only `proof`,
   `proof_deps`, and `proof_origin`; its separate Sheaf-wrapper attachment is
   preserved and is not claimed proved. For both delivered nodes, `proof_deps`
   equals the union of the proof steps' `uses`. The new node has its full
   statement, verbatim Lean signature, source, searches, creation record and
   chapter/unit. Corrected its stale `hSection` reference to the actually supplied
   `hBoundary`, and replaced its abbreviated blueprint provenance with
   `from.node`, the exact proof place, `via: []`, and `same_as: []`.

Second reading changed five redundant imports, the new node's hypothesis-name
reference and blueprint provenance, and the report's complete dependency-pruning
account. It also simplified identity derived vanishing using an existing proved
library theorem, specialized the induction helper directly, and abstracted the
explicit coordinate equivalence within its proof after compilation timeouts.
It replaced the unnecessary finite-edge-map equivalence by direct surjectivity,
transported module-stalk zero directly along an isomorphism, and factored the
exact derived-square proof through a proved private generic helper.
No existing public theorem statement or definition changed. The new generic
helper has a complete proof and introduces no additional hole.


Second-reading performance repair: several full-module checks hit the 60-second
limit before these reductions; the import-only diagnostic compiled in 5.9 seconds.
The assigned module additionally imports
`Sheaf.CategoryTheory.Abelian.ExactFunctorHigherDerivedVanishing` privately.
The original node's closed-section step and dependency union now cite the already
existing `lem-sc-exact-functor-higher-derived-vanishing`. The explicit scratch
`#print axioms` checks of both public declarations list exactly `propext`,
`Classical.choice`, `Quot.sound`, and the expected `sorryAx`.

Final local set compilation after the performance repairs passed cleanly: 4.5 s
for the new module and 56.3 s for the assigned module. The original public
signature remains byte-for-byte identical; both files meet the 100-character
line limit, and both dependency lists equal their proof-step unions.
