## Worker report

Item: lem-integral-ctf-equals-bc. Module: `Sheaf.Paper.IntegralCtfEqualsBc`.
The delivery has four theorem statements, each proved only by `sorry`, and five concrete
helpers for the scalar and constant-sheaf examples appearing in the node.
The nine declarations are all listed in `lean.declarations`. No definition contains `sorry`.

Read the current node and all six statement-dependency statements and records, their
recorded source declarations/docstrings, the nine proof-dependency records and sources,
and the current blueprint in `literature/blueprint/latest/blueprint/sec-proetale-coefficients/
sk-prop-integral-criterion/` (lemma, proof, and parent unit). The earlier stage-1 review's
finite constant scalar model convention is retained. The node text, accepted proof split,
and proof dependencies are unchanged. H2 of the return on 8596e957a115 correctly rejected
the added theorem statement dependency. It has been removed. The three scalar example
definitions now belong to this module, using the alternative explicitly authorized by
the maintainer. `det-def-localizing-closure-ctf-equals-bc` remains only in proof_deps,
and its module is a plain proof import. Relative to current main, the node changes
ONLY in lean; its stmt_deps and proof_deps are byte-for-byte the existing lists.

Hypothesis-by-hypothesis and clause-by-clause correspondence:

- A prime ell is `(ℓ : ℕ) [Fact ℓ.Prime]`. The existing `PadicAlgCl ℓ` supplies the fixed
  algebraic closure with its extended absolute value. A finite subextension is the existing
  `PadicAlgCl.FiniteIntermediateField ℓ`, not an arbitrary valued field. Its integer ring
  is `Profinite.padicIntegersRingObj ℓ E`, with the inherited valuation topology.
- A commutative condensed ring is `(Λ : Profinite.CondensedRing.{u})
  [IsCommMonObj Λ.X]`. The disjunction `hΛ` specifies exactly Z_ell, Q_ell, O_E, E, and Qbar
  by isomorphisms of ring objects, permitting arbitrary representatives. The Qbar choice
  is `Profinite.padicAlgClRingObj ℓ`, whose sections take values in a finite subextension;
  it is not the continuous-function ring of the unrestricted algebraic closure.
- A qcqs scheme is `(X : Scheme.{u}) [CompactSpace X] [QuasiSeparatedSpace X]`.
  The coefficient object is the dependency's `condensedRingObj Λ.X X = p_X^* Λ`.
  Module objects are the existing `Mod (Sheaf (Scheme.ProEt.topology X) Ab.{u+1}) ...`.
- Constructibility is exactly `IsConstantModelConstructible Λ.X X`. Its recorded
  definition uses a finite constructible locally closed stratification on qcqs schemes,
  with `HasFiniteConstantLocalModel` on each stratum. The latter is pulled from a finite
  scalar-matrix presentation on the condensed point, so it realizes the finitely presented
  scalar module convention. It does not substitute arbitrary sectionwise local finite
  presentation. The recorded constructibility module is imported publicly.
- Clause (1), including its integral torsion case, is the first conjunct of
  `integral_ctf_equals_bc`: every such module, embedded with `DerivedCategory.singleFunctor
  _ 0`, has `DerivedCategory.torAmplitudeIn _ (-1) 0`. The field implication's first
  conjunct gives `torAmplitudeIn _ 0 0` for Q_ell, finite E, or Qbar.
- Clause (2) is the second conjunct: `(a b : ℤ), a ≤ b`, membership in
  `constantModelBoundedConstructible Λ.X X`, and `homologyConcentratedIn a b K` imply
  `torAmplitudeIn _ (a - 1) b K`. The field implication's second conjunct instead gives
  `torAmplitudeIn _ a b K`, retaining the sharp field bound absent from the sibling's
  complex assertion.
- The universal test against EVERY degree-zero module M is the actual definition of
  `DerivedCategory.torAmplitudeIn`: it quantifies over all objects F of the module
  category and applies `homologyConcentratedIn` to `K ⊗ (singleFunctor _ 0).obj F`.
  The latter predicate means canonical-t-structure bounds, equivalently cohomology
  vanishing outside the closed integer interval. The monoidal structure here is the
  recorded relative K-flat derived tensor over Λ_X. No derived-completeness or test-module
  constructibility hypothesis is imposed.
- The final conjunct is equality of object predicates
  `(constantModelBoundedConstructible Λ.X X ⊓ DerivedCategory.finiteTorAmplitude _) =
  constantModelBoundedConstructible Λ.X X`. The dependency defines Dctf and Dbc as their
  full subcategories in exactly the same ordinary derived category, so this is the
  asserted equality with the same ambient morphisms.
- `integral_ctf_scalar_counterexample` asserts the owning module's
  `integralCriterionScalarExample ℓ`: the actual scalar quotient
  `integralCriterionScalarResidue ℓ` is finite, has no finite projective dimension, is not
  perfect in degree zero, whereas `integralCriterionScalarTwoTerm ℓ` is perfect under the recorded
  `DerivedCategory.IsPerfectRingComplex` definition. The added ring equivalence to
  `ZMod ℓ` identifies this quotient with F_ell. The concentration conjunct says the
  concrete complex has no cohomology outside [-1,0]; its two cohomology objects are
  explicitly isomorphic to that residue, by the last conjunct. Nonzeroness follows from
  this identification with ZMod of a prime; no nonregularity assumption is added.
- `integral_ctf_finite_ring_thick` has every finite commutative ring A, with the specified
  discrete topology, and every qcqs X. `IsTriangulated` and `IsStableUnderRetracts` of the
  bounded-constructible/finite-Tor intersection express precisely the parenthetical
  meaning of thick used by the node. Repleteness is already supplied by the recorded
  well-definedness theorem. This clause does not require ell-primary coefficients.
- `integralCriterionResidue` is the cokernel of ell times the identity of the actual
  regular coefficient module (the monoidal unit). Exact strong monoidal inverse image
  identifies this with the constant scalar quotient. `integralCriterionTwoTerm` is the
  image under `DerivedCategory.Q` of the mapping cone on ell times the identity of that
  unit in degree zero, hence the specified [A_X --ell--> A_X] in degrees -1,0. These are
  real constructions of the node's named examples, not arbitrary witnesses. They are
  helper declarations of this owning node as permitted by the brief; no independent
  mathematical notion or alternative constructibility/tensor definition is introduced.
- `integral_ctf_constant_counterexample` takes `(k : Type u) [Field k] [IsSepClosed k]`
  and the explicit `Scheme.Spec.obj (Opposite.op (CommRingCat.of k))`. Its conjuncts say
  the constant residue is constructible and has no finite Tor amplitude; the SPECIFIED
  two-term free complex is bounded constructible, has Tor amplitude [-1,0], is
  cohomologically concentrated in [-1,0], and has the constant residue as both
  cohomology modules. Finally its standard `truncGE 0` has no finite Tor amplitude.
  This explicitly witnesses the claimed possible failure of standard truncation
  stability; it is stronger than an unspecified existential witness only in spelling
  out the particular example already specified by the node.

Dependency declarations used (all names qualified by their actual namespaces):

| Node | Module | Declaration(s) used |
| --- | --- | --- |
| sk-def-sfb-condensed-ring | Sheaf.Topology.ProfiniteCondensedRing | Profinite.CondensedRing; reexported continuousMapRingObj |
| sk-def-sfb-qlbar-condensed | WeilConjectures.CategoryTheory.RingObjects.Condensed.EllAdic | Profinite.padicAlgClRingObj, padicIntegersRingObj; underlying padicAlgClCondensedRing |
| sk-def-sfb-pulled-back-coefficients | WeilConjectures.SixFunctors.ProEtale.ModuleObject.Basic | AlgebraicGeometry.ProEtale.coefficientRing, condensedRingObj, upperStarFromPoint |
| sk-def-sfb-constructible | Sheaf.Paper.ProfiniteFiniteConstantLocalModel | public dependency chain's AlgebraicGeometry.ProEtale.IsConstantModelConstructible, HasFiniteConstantLocalModel, constantModelBoundedConstructible |
| det-def-sfb-constructible-tor-amplitude | Sheaf.Paper.ConstantModelTorAmplitude | AlgebraicGeometry.ProEtale.constantModelConstructibleFiniteTor_wellDefined; existing DerivedCategory.torAmplitudeIn, finiteTorAmplitude |
| def-pc-perfect-ring-complex | Sheaf.CategoryTheory.DerivedCategory.PerfectRingComplexGeneral | DerivedCategory.IsPerfectRingComplex, used through integralCriterionScalarExample |
| det-def-localizing-closure-ctf-equals-bc (proof only) | Sheaf.Paper.LocalizingClosureCtfEqualsBc | AlgebraicGeometry.ProEtale.localizingClosure_ctf_equals_bc; plain import only |
| lem-sfb-padic-constant-local-model-tor | Sheaf.Paper.PadicConstantLocalModelTor | AlgebraicGeometry.ProEtale.padic_constant_local_model_tor |
| lem-sfb-stratified-tor-interval-devissage | Sheaf.Paper.StratifiedTorIntervalDevissage | AlgebraicGeometry.ProEtale.torAmplitudeIn_of_constructible_of_uniform_local_model |
| lem-sfb-cohomology-tor-interval | Sheaf.Paper.CohomologyTorInterval | AlgebraicGeometry.ProEtale.torAmplitudeIn_of_cohomology_interval |
| lem-sfb-square-zero-periodic-tensor | Sheaf.Paper.SquareZeroPeriodicTensor | ModuleCat.square_zero_periodic_resolution_tensor; AlgebraicGeometry.Scheme.square_zero_periodic_tensor |
| lem-sfb-constant-square-zero-tor-example | Sheaf.Paper.ConstantSquareZeroTorExample | AlgebraicGeometry.ProEtale.constant_square_zero_tor_example |
| lem-sfb-bounded-above-flat-kflat | WeilConjectures.FromJoel.CategoryTheory.Abelian.Flat.KFlat | CochainComplex.kFlat_of_isStrictlyLE_of_flat |
| sk-def-sfb-derived-tensor-hom | WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.Hom | AlgebraicGeometry.ProEtale.CondensedRing.derivedTensor, derivedHom; relative K-flat monoidal structure |

The existing constant-square-zero theorem and `constantResidueModuleOnSpec` specialize to
universe zero and hide the chosen cone behind an existential. The present node itself
specifies the cone and its cohomology and ranges over all separably closed fields. Its
helpers construct that cokernel and cone at `Scheme.{u}` directly. This does not rebind
or modify either sibling node, and it does not postulate any transport or map.

Edge cases checked mathematically before writing and on a second reading:

- Empty scheme and zero module/complex: all interval bounds are vanishing assertions;
  no Nonempty hypothesis excludes these cases. Empty stratifications are allowed by
  the existing predicate, not replaced by an original-open-stratum assumption.
- Negative cohomological endpoints, a=b (including a=b=0), and shifts: the integral
  lower endpoint is a-1 while the field endpoint remains a. Closed integer intervals
  [-1,0] contain exactly the two degrees in the explicit examples.
- Torsion scalar modules over O_E require degree -1; replacing [-1,0] by [0,0] would
  incorrectly exclude the residue field. The current statement keeps both bounds.
- ell=2, characteristic ell and characteristic different from ell for k are included;
  no invertibility or characteristic assumption is introduced on the base scheme.
- The finite-ring thickness clause includes the zero ring and does not accidentally
  restrict A to a field, an ell-primary ring, or a nonzero ring.
- Both the scheme and separably closed field use the explicit same universe u. For the
  fixed small ring ZMod(ell²), use `continuousMapRingObj.{u}`: its site universe is
  independent of its Type-0 scalar carrier. For the arbitrary A : Type u finite-ring
  clause, use the published `continuousCoefficientRingObj A`. The first compiler pass
  caught the scalar/site-universe coupling and it was repaired without restricting u.

Searches made before defining anything:

- `msearch.py ... leanfinder "Constructible condensed p-adic module sheaves have Tor
  amplitude minus one to zero, bounded constructible complexes have finite Tor amplitude"`:
  eight hits (CondensedMod.IsSolid, LightCondensed Grothendieck instance, generic derived
  cohomological bounds and representatives); none states this result.
- `msearch.py ... loogle '"torAmplitudeIn"'`: successful search, zero hits.
- `msearch.py ... grep 'torAmplitude|ctf_equals_bc|integral.*ctf'`: six incidental substring
  hits in Mathlib, no constructible condensed Tor theorem.
- `rg` over both `lean/WeilConjectures` and `lean/Sheaf` for integral_ctf, integralCtf,
  ctf_equals_bc, constructible Tor, and the item ID found the sibling
  `localizingClosure_ctf_equals_bc` and consumers. Its definition and full theorem were
  read. It supplies the common [-1,0]/[a-1,b] bounds and field MODULE bound, but not
  the field COMPLEX [a,b] bound nor the explicit cohomology identifications in this node.
  It remains a proof dependency, not a statement dependency or an exact existing
  statement binding for the whole item.
- `rg` for TwoTerm/twoTerm/two_term, constantResidue, scalarResidue found the scalar
  examples in that sibling and private twoTerm constructions in ConstantSquareZeroTorExample.
  The private definitions cannot be named by consumers, and its public theorem hides the
  cone behind an existential and uses universe zero. The present concrete helpers are
  the specified examples at arbitrary scheme universe; they do not duplicate a usable
  exported general construction.
- Name-clash searches over Mathlib, WeilConjectures, Sheaf, and dag/lean_names_upstream.json
  for the six original and three new delivered declaration names found none.

No new statement dispute is raised. No source-based statement correction or new DAG node
is needed. The ordinary uncompleted and finite constant model conventions are explicit.

Validation of the returned version: prescribed scompile.py compiled in sandbox and actual
library module modes, in 11.0 s and 8.0 s respectively. This is historical validation only;
the repaired module is compiled and dry-run again before re-delivery. Every theorem proof
is still `by sorry`; all nine declaration bodies and signatures were checked for forbidden
local notation, implicit universes, and hollow data.

## Second reading by NF

A second complete pass by the same dispatcher-started worker compared the node and file;
no independent worker was started, as the assignment explicitly forbids other agents.
The maintainer's independent review remains the required independent reading.

The comparison checked the coefficient disjunction against all five coefficient choices,
finite subextensions versus arbitrary subfields, the finite-subextension-valued Qbar,
qcqs, and each quantitative interval. It checked the sharp field complex clause separately
from the field module clause (the existing sibling only states the latter explicitly).
It unfolded the existing Tor predicate on paper to check that arbitrary degree-zero module
sheaves, including nonconstructible tests, are quantified. It checked that the equality is
of predicates in one ordinary derived category and that no completeness data are required.
For the examples it checked integralCriterionScalarResidue's definition, the mapping-cone
degrees, both cohomology identifications and nonperfectness in integralCriterionScalarExample. It checked the
finite-ring clause has no prime-primary restriction, and the final example specifies the
actual cone with its truncation failure, for k in Type u. The first-pass universe fault
in the constant example was corrected using the existing continuousMapRingObj.{u}, then
the full module compiled cleanly. No hypothesis or conclusion was changed to fix it.

Historical check of the returned version: `deliver2.py NF lem-integral-ctf-equals-bc --no-push` returned
`OK (dry run): commit 8b0bb3f6ff9 passes the preflight and compiles; nothing pushed`.


## Repair of H2 on returned head 8596e957a115

The return identifies one fault, H2: a theorem node was added as a statement dependency
solely to obtain three definitions in its module. The maintainer explicitly permits
putting those definitions in this item's module and dropping that statement dependency.
This repair takes that option and does not add a new node.

- Removed `det-def-localizing-closure-ctf-equals-bc` from stmt_deps. The resulting list
  matches current main exactly. Its occurrence in proof_deps and the proof plan remain.
- Changed the sibling module from `public import` to plain `import`, so it supplies
  proof material only. Publicly imported `WeilConjectures.RingTheory.GlobalDimension`
  and `Mathlib.Topology.Instances.ZMod` supply the scalar definitions' actual types.
- Added `integralCriterionScalarResidue`: the actual quotient of `ZMod (ell^2)` by the
  ideal generated by ell. It has the same data as the previously referenced scalarResidue.
- Added `integralCriterionScalarTwoTerm`: the actual derived image of the cone on
  multiplication by ell of the degree-zero regular module. Multiplication is constructed
  directly by `ModuleCat.ofHom (LinearMap.mulLeft A (ell : A))`; no sibling helper
  is needed in this definition.
- Added `integralCriterionScalarExample`: the four assertions of finiteness of the quotient,
  its failure of finite projective dimension, perfectness of the specified cone, and
  nonperfectness of the quotient in degree zero. It uses the existing perfect-complex
  definition. The scalar counterexample theorem now names these owning-module helpers.
- Recorded all nine declarations in lean.declarations; each new helper has a source and
  `(blueprint: lem-integral-ctf-equals-bc)` docstring. All data are concrete, without
  new proof obligations, axioms, `sorry` definitions, or an arbitrary chosen example.

Comparison with returned head: the retained sandbox was the delivered version; its
added stmt_dep and public sibling import were present and its scalar theorem referenced
the sibling's three names. Those are precisely the structures repaired above. Comparison
with current main shows that the item's only modified JSON field is lean; statement,
stmt_deps, proof, proof_deps, and all other metadata are unchanged. The delivery wrapper
refreshes main and constructs the final rebased commit; no direct git command was run.

Second pass on the repair checked that the three new concrete definitions expand to the
same quotient, map and four scalar predicates used by the returned theorem. The main
coefficient theorem signature, finite-ring theorem, constant examples, all quantifiers,
and all numerical bounds remain unchanged. The scalar counterexample merely names the
owning module's definitions. H2 is repaired without a mathematical statement correction.
The maintainer's return already independently accepted the mathematics of every clause.

Repaired-file validation: the prescribed scompile.py compiled both sandbox mode
(19.4 s) and actual module mode (9.9 s) cleanly, with no errors or warnings. The first
repair compile identified one long module-docstring line; it was shortened before this
clean final compile. The primary signature matches lean.statement verbatim, and the
file has four sorry-only theorem proofs and five concrete definition/abbreviation bodies.
