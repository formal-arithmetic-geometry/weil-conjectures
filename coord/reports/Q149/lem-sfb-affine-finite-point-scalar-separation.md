## Worker report

The module `Sheaf.AlgebraicGeometry.AffineFinitePointScalarSeparation` states
`AlgebraicGeometry.Scheme.exists_globalSection_zero_on_finite_ne_zero` with a whole-proof
`sorry`. It adds no definitions, dependency modules, or nodes, and changes only the item's
`lean` record. No statement correction or disputed statement is needed.

Clause-by-clause correspondence:

- The affine scheme is `(X : Scheme.{u}) [IsAffine X]`. The universe `u` is explicit and
  unrestricted. Mathlib's `IsAffine` means the canonical `X → Spec Γ(X, ⊤)` is an isomorphism,
  equivalently the affine-scheme notion of the node.
- The finite subset of underlying points is `(F : Set X) (hF : F.Finite)`; `X` coerces to its
  underlying point type. Finiteness is a hypothesis, with no closed-point assumption.
- The distinguished point is `(z : X)`.
- The entire separation hypothesis is
  `(hz : ∀ x ∈ F, z ∉ closure ({x} : Set X))`. The singleton closure is taken in the scheme's
  underlying Zariski topology, with precisely the specialization direction of the node.
- The required global regular function is `∃ f : Γ(X, ⊤)`.
- Vanishing at every point of the finite set is `(∀ x ∈ F, X.Γevaluation x f = 0)`.
- Nonvanishing at the specified point is `X.Γevaluation z f ≠ 0`, conjoined with that vanishing.
- The node's explanation of `f(y)` is rendered by the existing `X.Γevaluation y`: this is
  `X.evaluation ⊤ y trivial`, whose definition is the top-open germ map followed by
  `X.residue y`. The latter is the quotient map to
  `IsLocalRing.ResidueField (X.presheaf.stalk y) = X.residueField y`. Thus the equations live
  in each point's own residue field, without imposing a common coefficient field.

Dependencies read and used:

- `def-pc-scheme`: `Mathlib.AlgebraicGeometry.Scheme`, declarations
  `AlgebraicGeometry.Scheme` and `AlgebraicGeometry.Scheme.Hom`; the former provides the
  scheme and underlying point type. Their full definitions/docstrings were read.
- `def-weil-residue-field`: `Mathlib.AlgebraicGeometry.ResidueField`, declarations
  `AlgebraicGeometry.Scheme.residueField` and `AlgebraicGeometry.Scheme.Hom.residueFieldMap`.
  The residue field and its evaluation map are used; the induced field map clause of this
  dependency is not needed by this item. Read `residue`, `evaluation`, and `Γevaluation` too.
- The three proof dependencies are already Mathlib leaves and need no Lean-record repair.
  `lem-weil-pbc-affine-open-spec-points` records `IsAffineOpen.fromSpec`,
  `isOpenImmersion_fromSpec`, `range_fromSpec`, `primeIdealOf`, and `fromSpec_primeIdealOf`
  in `Mathlib.AlgebraicGeometry.AffineScheme` (namespace `AlgebraicGeometry`).
  `lem-weil-pbc-spec-irreducible-closed-subsets-primes` records
  `PrimeSpectrum.closure_singleton` and `PrimeSpectrum.pointsEquivIrreducibleCloseds`
  in `Mathlib.RingTheory.Spectrum.Prime.Topology`.
  `lem-weil-pbc-affine-open-section-vanishing-prime` records
  `Scheme.evaluation_eq_zero_iff_notMem_basicOpen` in the residue-field module,
  `IsAffineOpen.fromSpec_preimage_basicOpen`, `fromSpec_primeIdealOf`, `basicOpen`,
  `isLocalization_basicOpen` in the affine-scheme module, and `PrimeSpectrum.mem_basicOpen`
  in the prime-topology module. The relevant source signatures and documentation were read.
  The statement dependencies are public imports; prime topology is also explicitly imported
  as a proof dependency. The proof docstring reproduces all three steps of the DAG proof.

Source grounding: read `literature/stacks-project/properties.tex`, lines 5326–5381,
Tag 0F20, especially the induction step's removal of the earlier points' closures and its
explanation that the new point is not their specialization. The affine finite-product
construction in the accepted DAG proves precisely the scalar assertion stated here.
The compact-object example module is now withdrawn; its node points to
`WeilConjectures.CategoryTheory.CompactObject`, whose source was read for the current style.

Edge cases checked before writing:

- `F = ∅`: the condition and vanishing clause are vacuous; `f = 1` is nonzero in the
  residue field at `z`. The statement does not require `F` nonempty.
- The empty scheme: there is no possible `z : X`; no scheme is excluded by an added axiom.
- If `z ∈ F`, reflexivity of singleton closure makes the hypothesis impossible, as intended.
- Nonclosed points are allowed. On `Spec A`, `z ∈ closure {x}` means `p_x ⊆ p_z`;
  its negation supplies a factor in `p_x` outside `p_z`, rather than the reverse direction.
- Nonreduced rings and all characteristics are allowed. Ideal membership, prime properness,
  and the finite-product argument need neither reducedness nor a field structure on `A`.
- A mere subset with a finiteness proof avoids enumeration, decidable equality, or distinctness
  assumptions. There is no independent index universe or hidden auto-bound variable.

Searches for an existing statement (all through the prescribed `msearch.py` where applicable):

- LeanFinder: "On an affine scheme find a global regular function vanishing at each point of
  a finite set and nonzero at a point outside the closure of each point". Eight hits included
  `exists_pow_mul_eq_zero_of_res_basicOpen_eq_zero_of_isAffineOpen`,
  `StructureSheaf.normalize_finite_fraction_representation`, `Scheme.affineBasicOpen`,
  `IsAffineOpen.exists_basicOpen_le`, and restriction/clearing-denominator statements.
  No returned statement asserts the finite-point separation theorem.
- LeanSearch: "An affine scheme admits a global function zero on a finite set of points and
  nonzero at a point outside their closures". Eight hits included `Scheme.toSpecΓ_image_zeroLocus`,
  the evaluation/basic-open criteria, and zero-locus/ideal-sheaf results; none is the entire lemma.
- Loogle: `AlgebraicGeometry.IsAffine, "evaluation"`. No hits.
- Mathlib grep: `evaluation_(eq_zero|ne_zero)_iff|exists.*(finite|finset).*(evaluation|basicOpen)`
  in `AlgebraicGeometry`. Three hits, all the evaluation/basic-open criteria or their proof;
  these provide existing notions and individual proof ingredients, not the target assertion.
- Direct `rg` of `lean/WeilConjectures`, `lean/Sheaf`, and `dag/lean_names_upstream.json`
  for affine finite-point/scalar-separation names and existence/evaluation patterns found
  unrelated evaluation statements, with no exact match. A focused `Γevaluation` and
  evaluation/closure search of both algebraic-geometry trees was inspected: the hits concern
  point evaluation, local charts, residue comparisons, or other constructions.
- `grep -rn 'lem-sfb-affine-finite-point-scalar-separation' lean/WeilConjectures` had no hits.
  The chosen full declaration name was also searched in Mathlib, both source trees, and
  the upstream-name index and had no hits.

## Second reading by Q149

A separate pass by the same worker reread the node and the complete module; no other agent
was started, as required by the dispatch brief. Independent review is left to the maintainer.
The checks matched `Scheme.{u}` plus `IsAffine X` to the affine scheme, `F : Set X` plus
`F.Finite` to the finite set, `z : X` to the arbitrary distinguished point, and `hz` to
nonmembership in each singleton closure. The existential ranges over global sections,
its first conjunct quantifies over exactly `F`, and the second evaluates at exactly `z`.
Reading the definitions of `Γevaluation`, `evaluation`, and `residue` confirms the node's
specified germ-then-residue value rather than a stalk-valued vanishing condition.
The closure direction and the empty-product case in the proof docstring agree with the
accepted DAG proof. All theorem binders and `u` are explicit. No mismatch was found and
no statement or dependency correction was made.

Validation: the prescribed `scompile.py Q149 lem-sfb-affine-finite-point-scalar-separation`
completed successfully for this file in sandbox mode and its actual library-module mode,
with no error or warning output. The source has no lines over 100 characters and exactly
one `sorry`, the whole proof of the named theorem. Delivery preflight is run by `deliver2.py`.
