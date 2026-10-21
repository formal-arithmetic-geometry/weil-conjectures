## Worker report

Module: `Sheaf.Algebra.Homology.PerfectTensorRoosCompletion`.
Main declaration: `CochainComplex.PerfectTensorRoos.perfect_tensor_roos_completion`.
The companion declarations recorded in `lean.declarations` are part of this item's
statement: in particular `derived_completion`, `tensor_coherence`,
`scalar_extension`, `ramified_extension`, and `scalar_identity_composition`.
All postponed proofs are named theorems with source and proof docstrings. Definitions
contain actual data. The two choices of comparison maps use existence AND uniqueness
with their quotient or both product coordinates fixed; they do not choose an arbitrary
isomorphism from a mere existence statement.

The mathematical sources were read in `literature/stacks-project/sites-cohomology.tex`,
Tag 0941, `lemma-derived-limit-is-ok`, and `algebra.tex`, Tag 031B,
`lemma-when-finite-module-complete-over-complete-ring`. The node's own twelve-step
finite-projective retract and coordinate argument is transcribed into the main theorem's
docstring; companion proofs spell out the corresponding construction and coherence steps.

### Hypotheses and objects

- The base ring is `{R : Type u} [CommRing R]`, with `[IsDomain R]` and
  `[IsDiscreteValuationRing R]` in the completion assertions. A uniformizer is
  `(π : R) (hπ : Irreducible π)`, using the recorded Mathlib DVR characterization.
- Completeness is `[IsAdicComplete (Ideal.span {π}) R]`, namely separatedness and
  completeness for the quotient modules. It is the stated bijection with the limit,
  not a valuation or norm completeness hypothesis.
- `P Q : CochainComplex (ModuleCat.{u} R) ℤ` are the given representatives.
  `FiniteProjective P` unfolds to the existence of bounds `IsStrictlyGE a` and
  `IsStrictlyLE b`, and `Module.Projective R (P.X i)` and `Module.Finite R (P.X i)`
  in every degree. This is a shorthand for the representative data, not another
  definition of perfect derived objects. Derived perfectness uses the recorded
  `DerivedCategory.IsPerfectRingComplex`.
- The signed total tensor `P ⊗ Q` is the published cochain monoidal tensor, with
  `HomologicalComplex.ιTensorObj` for its bidegree injections. No new totalization
  or derived tensor definition is introduced.
- The index `n : ℕ` denotes the node's positive index `j=n+1`. The quotient ring is
  `R ⧸ (Ideal.span {π})^(n+1)`. `quotientTensor` is precisely the tensor OVER THAT
  QUOTIENT of the two termwise scalar extensions, restricted back to R.
  Mathlib puts the scalar in the first position, `a ⊗ₜ[R,f] x`, rather than `x ⊗ a`.
- `towerFunctor`, `tower`, and `quotient` use the already published module quotients,
  projections and strict quotient transitions. The balanced isomorphisms in the main
  theorem identify the quotient tensor `U_j` with this quotient tower of `V`.
  Thus the Roos construction is written after the canonical balanced identification
  `U_j ≅ V/π^j V`; it is not an unrelated replacement tower. The pure-tensor formula
  determines these identifications and their compatibility with all transitions.
- `augmentation` is the actual published `roosAugment`, with the actual quotient maps
  and their compatibility theorem. `completion = tower ⋙ roosF`; no arbitrary map
  to an unspecified derived limit is a hypothesis.
- The existing Roos model has coordinates `(y,x)` in degrees `(q-1,q)` and differential
  `(-dy-(1-t)x,dx)`. Reordering and negating the shifted coordinate gives the node's
  `(x,-y)` coordinates and differential `(dx,(1-t)x-d(-y))`. Consequently zero in the
  first published coordinate is exactly the required zero shifted coordinate.

### Conclusions, clause by clause

| Node clause | Lean rendering |
| --- | --- |
| Bounded finite projectivity of V | First conjunct of `perfect_tensor_roos_completion`, `FiniteProjective (P ⊗ Q)` |
| Balanced isomorphism U_j to V tensor A_j | Second conjunct: an actual cochain isomorphism from `quotientTensor` to the quotient of `P ⊗ Q`, with the formula for every bidegree, x, y and representatives a,b |
| Formula `(x⊗a)⊗(y⊗b) ↦ (x⊗y)⊗ab` | The image is `a • b • mkQ (ιTensorObj ... (x ⊗ₜ[R] y))`; `scalar_tensorator_formula` also gives the balanced multiplication formula for arbitrary scalars in any target ring |
| Surjective strict quotient transitions | Third conjunct, `Function.Surjective` for every degree and consecutive tower map |
| Termwise inverse limit V with the specified projections | `Nonempty (IsLimit (quotientCone ... (P ⊗ Q)))`; the cone vertex and all its projections are defined, not existentially chosen |
| Degreewise surjectivity of 1-t | `Function.Surjective ((roosU ...).f q)` |
| Its kernel is exactly the quotient image, with injective quotient map | The next conjunct gives `Function.Injective (Pi.lift ...).f q` and `LinearMap.range ... = LinearMap.ker ...` |
| Specified e is a quasi-isomorphism | Last conjunct, `QuasiIso (augmentation ... (P ⊗ Q))` |
| Both coordinates of e | `augmentation_coordinates`: its `roosχ` image is `biprod.lift 0 (Pi.lift quotient).f`; evaluation at every level is exactly `quotient` |
| Canonical ordinary derived tensor completion | `derived_completion` uses the existing derived tensor, asserts invertibility of its localization tensorator and of `Q.map augmentation`, and asserts derived perfectness |
| Canonical derived inverse-limit interpretation | Last clause of `derived_completion`: for any normalized total right derived limit `(RF,η)`, a comparison σ is fixed by the equality with `Q.map roosAugmentLimit ≫ η.app tower` |
| Naturality and independence of projective models | `augmentation_coordinates` gives strict naturality and preservation of homotopies. `derived_completion` quantifies over every other pair of finite projective models and EVERY derived morphism a, with the unique intertwining morphism b between their completions |
| Associator, Koszul symmetry, both multiplication unitors | `tensor_coherence` states `Square` for the published `α_`, `β_`, `λ_`, `ρ_`; these are the signed cochain tensor constraints, and `Square` is the actual coaugmentation naturality equation |
| Coefficient unit | Last clause of `tensor_coherence` evaluates the coaugmentation of the tensor unit at each level as its quotient projection. The coefficient 1 is thereby reduced to 1 |
| Every further quotient, m≥n≥1 | Last clause of `augmentation_coordinates` gives equality with `AdicCohomology.transition` for EVERY `n≤m`, not only adjacent levels |
| Finite-free scalar comparison | `scalarProduct` is defined by its extended product projections followed by the uniquely normalized balanced `scalarQuotientIso`; `ScalarCoordinates` prescribes BOTH cone coordinates, and uniquely determines `scalarComparison` |
| Balanced scalar tensorator | `scalarTensorator` is the inverse of the published oplax monoidal total comparison for ordinary extension. `scalar_tensorator_formula` asserts it is invertible and gives multiplication of the two scalar entries on pure tensors |
| Compatibility with finite-free extension | `scalar_extension` gives invertibility of the product and Roos comparisons, both coordinates, the scalar coaugmentation equation, and the square with the balanced tensorator |
| Naturality of the scalar comparison | `scalar_naturality` is the equality for every map of representatives, with its descent described in the proof docstring |
| Local extension of complete DVRs | `ramified_extension` has `[Algebra R S]`, `[IsLocalHom (algebraMap R S)]`, `[Module.Free R S]`, `[Module.Finite R S]`, both DVRs, irreducible uniformizers, both adic completeness instances, and the original two finite-projective representatives |
| Continuity | For these adic DVR topologies locality and finite freeness imply `π=u σ^e` with e≥1, so the map is automatically continuous. No independent topological structure or stronger continuity assumption is imposed |
| Cofinal comparison of the two filtrations | `ramified_extension` supplies e≥1 and a unit with `π=u σ^e`, and θ from the arithmetic restriction of the σ-tower to the π-tower, fixed by EVERY quotient projection |
| Induced canonical derived completion comparison | Its δ is an isomorphism characterized by `δ.hom ≫ Q.map (arithmetic ≫ roosF.map θ.hom) = Q.map scalarComparison`; it is exactly scalar comparison followed by inverse cofinal restriction |
| Ramified augmentation and tensor squares | The two further equalities for δ give the ordinary coaugmentation square and the balanced tensorator square |
| Identity and iterated extension | `scalar_identity_composition` gives the actual two equations using `extendId`, `extendComp`, and `idealCongr`. `arithmetic_coherence` gives identity and composition of the cofinal maps, with index transports expressed by `HEq`. Since δ is determined by its displayed equation with an invertible map, these equations give its identity/composite squares as well |
| Quotient and zero shifted coordinates in these squares | `ScalarCoordinates`, `augmentation_coordinates` and the selection/block coordinate and augmentation equations in `arithmetic_coherence` retain both coordinates before localization; block sends zero to zero |

`HasDerivedCategory.{w}` binders expose the library's independent localization universe.
They are the standard existence interfaces for D(R), not restrictions on the rings or
complexes. Ring/module/scalar-extension universes are shared `u`, permitting every ring
and its finite extensions by choosing a common universe; `autoImplicit` is disabled.
The right-derived-limit comparison exposes its usual normalization on K-injectives,
as in the recorded exact-products Roos comparison.

### Dependency declarations used

The original statement dependencies were read, including full signatures and docstrings:

- `Sheaf.CategoryTheory.DerivedCategory.PerfectRingComplexGeneral`:
  `DerivedCategory.IsPerfectRingComplex` (and its bounded projective model data).
- `Mathlib.Algebra.Homology.DerivedCategory.Basic`: `DerivedCategory`,
  `DerivedCategory.Q`, `HasDerivedCategory`.
- `Sheaf.CategoryTheory.RingedStrictTowerHomotopyLimitIndependentCoefficients`:
  `CategoryTheory.ringedStrictTowerHomotopyLimitIndependentCoefficients` (one-point
  specialization is realized with the published ordinary module Roos model).
- Recorded tensor match `CochainComplex.mapBifunctor` /
  `HomologicalComplex.mapBifunctor`, and the published
  `WeilConjectures.Mathlib.Algebra.Homology.Monoidal` monoidal structure:
  `HomologicalComplex.ιTensorObj`, its signed braiding and monoidal constraints,
  `Functor.OplaxMonoidal.mapHomologicalComplexδNatTrans`.
- Mathlib's `IsDiscreteValuationRing`, `Irreducible`, `Module.Projective`,
  `Module.Finite`, and `IsAdicComplete`.

The actual construction owners in `stmt_deps` are now:

- `def-sf-adic-module-quotient-data` (`existing: true`), module
  `Sheaf.Algebra.Homology.AdicShortComplexCohomologyML`:
  `AdicCohomology.power`, `.quotient`, `.projection`, `.transition`.
- `def-weil-strict-roos-model`, module `Sheaf.CategoryTheory.StrictRoosModel`:
  `CategoryTheory.roosP`, `roosU`, `roosF`, `roosχ`, `roosEval`, `roosAugment`,
  `roosAugmentLimit`, `roosLimitFunctor`.
- `def-sf-strict-roos-square-map` (`existing: true`), module
  `Sheaf.CategoryTheory.StrictRoosAdditiveComparison`:
  `CategoryTheory.strictRoosMapOfSquare`, its coordinate characterization,
  and the helper `strictRoosBlock_comm` for the arithmetic specialization.
- `def-sp-strict-tower-arithmetic-restriction-data`, module
  `Sheaf.CategoryTheory.StrictTowerArithmeticRestrictionDefs`:
  `CategoryTheory.StrictTowerArithmetic.index`, `complexRestriction`, `selection`, `block`.

The first and third records supply the missing definition-node ownership of existing
plain definitions, as expressly permitted by the return's `existing: true` option.
No Lean declaration is duplicated, moved, or given new data. The arithmetic definitions
already have an owner; that existing node is cited directly. The theorem nodes
`lem-sfb-adic-short-complex-cohomology-ml`, `lem-pur-roos-additive-comparison`, and
`lem-sp-strict-tower-arithmetic-restriction` are removed from the additions to
`stmt_deps`. Their mathematical results are in the proof layer only; none is a new
hypothesis or a source of data. The base `proof` and `proof_deps` are retained verbatim
(the base did not list these three theorem nodes directly). In particular, the existing
`lem-pur-compact-support-roos-cofinality` proof dependency supplies the arithmetic
cofinality theorem and imports the additive-comparison/arithmetic theorem modules.
The ML conclusion of the adic theorem is not used in this item.

The item-specific wrappers, coordinate predicates and canonical comparisons still belong
to this node's specified quotient tensor completion diagrams. There are no dependency
interface repairs or mathematical statement corrections.

The modules of the recorded proof dependencies with usable declarations are imported
non-publicly: surjective module-complex tower limits, bounded-flat K-flatness, derived
monoidal structure, K-flat scalar tower realization, exact-products Roos comparison,
small-module diagrams Grothendieck, compact-support Roos cofinality, K-projective
localization, and flatness. The finite-free strict-tower-transport proof dependency has
no recorded Lean declaration; the needed canonical comparisons are explicitly supplied
here with their quotient/product normalization, without waiting on that proof dependency.

### Edge cases checked

- The zero complex and zero terms are permitted; the finite-projective predicate does
  not demand positive rank, nonzero modules, or nonempty support intervals.
- Negative cochain degrees and arbitrary integer support endpoints remain included.
- `n=0` means j=1, so the zero-power quotient is never silently substituted for A_1.
  Further reduction includes the equality case m=n.
- The bounded tensor is a finite sum degreewise; no unbounded-product tensor
  commutation is assumed. The quasi-isomorphism applies to the specified map.
- The coefficient tensor unit is included, with both left and right unitors.
- The arithmetic restriction requires e≥1, includes e=1, and composes with factor ef.
  A local finite-free extension between domains has positive rank and nonzero image
  of π; no zero or negative ramification exponent is used.
- Unramified maps, the identity extension, iterated extensions, arbitrary derived
  morphisms and changes of representatives are all quantified; no chosen-basis or
  chosen-cochain-map restriction is imposed.
- Scalar quotient/comparison constructions make sense without flatness; invertibility
  of the infinite-product comparison is asserted under finite freeness.
- Defining a comparison by unique coordinates fixes its data up to actual equality,
  meeting the no-hollow-definition rule. The main augmentation is a direct construction.

### Searches

Prescribed wrapper:
`python3 /home/ubuntu/weil-launcher-all/batch2/msearch.py Q65 lem-sf-perfect-tensor-roos-completion`.

- `leanfinder`: “The tensor of bounded finite projective complexes over a complete DVR
  is canonically quasi-isomorphic to the Roos complex of its quotient tensor tower”.
  Eight hits, including ordinary `AdicCompletion` finite-Noetherian tensor comparison
  and general tensor facts; no matching quotient Roos coaugmentation with coherence.
- `loogle`: `CochainComplex, TensorProduct, IsAdicComplete`. Zero hits.
- `grep`: `roos|Roos|[Cc]ompletion`, subdirectory `Algebra/Homology`. One irrelevant
  idempotent-completion result in `LeftResolution/Reduced`; no matching theorem.
- `rg` in both project source trees for perfect/Roos/completion/tensor combinations,
  and the exact item id; also the prescribed `grep -rn` of the item in
  `lean/WeilConjectures`. No existing theorem for this item. Searches did locate the
  existing quotient, Roos, arithmetic and additive comparison modules reused above.
- Follow-up `rg` for `extendScalars.*[Aa]dditive` found the published adjunction formula
  `(ModuleCat.extendRestrictScalarsAdj f).left_adjoint_additive`; definitions use that
  actual proof term internally, rather than a new axiom or a file-local instance.
- Source searches for monoidal cochain comparison and functor lifting found
  `NatIso.mapHomologicalComplex`, `Functor.mapHomologicalComplexIdIso`, and
  `Functor.mapHomologicalComplexCompIso`, used for the canonical scalar transports.

No `STATEMENT-DISPUTED` flag: no counterexample or node fault was found.

### Validation

The initial saved packet passed the required `deliver2.py --no-push` against current
main: `OK (dry run): commit 7ff24c2c571 passes the preflight and compiles; nothing pushed`.
The explicit `scompile.py` check passed with no errors or warnings in sandbox (31.7 s)
and library-module (34.7 s) forms. The repaired ownership packet passed a further dry run:
`OK (dry run): commit a62a847406f passes the preflight and compiles; nothing pushed`.
The Stacks tag map and actual source text were checked: 08TC is
`derived.tex`, `definition-derived-limit`; 0H9K is `more-algebra.tex`,
`lemma-pro-isomorphism-iso-Rlim`. All compilation uses `scompile.py` or the
required delivery wrapper, never a local/global lake build.

## New nodes

`def-sf-adic-module-quotient-data` records the existing additive functors
`M ↦ M / I^n M`, the map on morphisms, and their natural projections and transitions
at every `n : ℕ`. The source is the ordinary quotient system of Stacks Tag 031B and
the quotient towers used in Tag 0941. LeanSearch and LeanFinder found ordinary adic
completion and transition maps, Loogle found `Submodule.mapQ_eq_factor`, and Mathlib
grep found no categorical quotient functors in `Algebra/Category/ModuleCat`.
Project searches found the precise existing `AdicCohomology` declarations. DAG searches
found no definition node owning these names; `def-weil-pbc-quotient-module` provides
individual module quotients and is cited. The general-site sheafified quotient node is
a different construction. The blueprint search found no matching node. Accordingly the
new record is `existing: true` on the existing module, with no new Lean file.

`def-sf-strict-roos-square-map` records the actual shifted cone map of a commuting square
of Roos endomorphisms, with its two diagonal coordinates and the selection/block
specialization. It cites the existing strict Roos model and arithmetic restriction
definition nodes. The source is Stacks Tag 0941 and the cone/arithmetic constructions
of Tags 08TC and 0H9K. LeanSearch/LeanFinder found general mapping-cone maps; Loogle
reported the unqualified helper unknown; Mathlib grep found the underlying
`homotopyCofiber.mapArrowHom`. Project searches found the exact existing
`strictRoosMapOfSquare` and its proved coordinate/telescoping lemmas in
`StrictRoosAdditiveComparison`. No definition node owns these declarations, and the
blueprint search found no matching node. The existing strict Roos definition covers
tower-map induced diagonal maps, rather than two independent square entries. This
new ownership record is also `existing: true`, without duplicating a declaration.

## Return repair and self-check

The immutable returned head is `29d7d53c90e5`. H2/C5 is repaired by the two definition
ownership nodes above and by the direct arithmetic-definition citation. The retained
Lean file is byte-identical to the saved packet: its mathematical clauses were approved
in the return. The node's original statement, proof, and proof dependencies are likewise
unchanged; only its `lean` record and added definition dependencies change.

The self-check compared every clause to the existing node and file. The main theorem
binds a complete DVR with irreducible uniformizer and two bounded finite-projective
complexes, asserts finite projectivity of their signed tensor, fixes the balanced iso
on every pure tensor, gives degreewise quotient surjectivity, the specified quotient
limit cone, surjectivity and kernel of `1-t`, and quasi-isomorphism of the specified
augmentation. `augmentation_coordinates` retains zero shifted coordinates and every
further quotient. `derived_completion` fixes its comparison by the normalized unit and
quantifies over every derived morphism and replacement model. `scalar_extension`,
`ramified_extension`, and `scalar_identity_composition` keep the balanced tensorator,
positive exponent, cofinal maps and identity/composite equations. Zero complexes,
level one (`n=0`), equal quotient levels, and ramification exponent one remain allowed.
The two new existing records were read against full source definitions: quotient maps
send `[x]` to `[f(x)]` or `[x]`, projection sends `x` to `[x]`; the cone map is literally
`homotopyCofiber.mapArrowHom` shifted by `-1` and its coordinates are `(b,a)`.

The tensor-coherence observation in the return was advisory: the `Square` clauses are
the strict naturality instances for the published signed constraints; the file also
states the balanced scalar tensorator on arbitrary pure tensors in
`scalar_tensorator_formula`. No stronger monoidal-comparison claim is introduced in
this ownership repair.

## Second reading by Q65

This section records the worker's actual self-check above, not an independent review.
The dispatched-worker instruction forbids starting another agent; the maintainer supplies
the independent reading. The concrete mismatch found was definitional ownership, repaired
in the item dependencies and two new records. The Lean hypotheses and conclusions were
read against the node as described above; no other mismatch was found in this repair.
