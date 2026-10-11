## Worker report

The module `lean/Sheaf/RingTheory/JacobiZariskiHomologySequence.lean` states
`Algebra.jacobiZariski_homology_sequence`, with its sole proof `by sorry`.
There are no new definitions, dependency modules, or changes to the mathematical node.

Source read: [Stacks Project, Tag 00S2](https://stacks.math.columbia.edu/tag/00S2),
Lemma 10.134.4, statement and entire proof. The local literature checkout is not present
on this machine; the source was read online. The source explicitly requires both Tor_1
and Tor_2 vanishing and imposes no finiteness, smoothness, or flatness assumption.

Hypothesis and clause correspondence:

- Arbitrary commutative rings A, B, C: three independent universes `u v w` and the three
  `CommRing` binders. The maps A → B → C are `Algebra A B` and `Algebra B C`;
  `Algebra A C` together with `IsScalarTower A B C` specifies exactly the composite,
  not an extra mathematical hypothesis.
- The canonical presentation A[B] → B is `Generators.self A B`; `P` is its
  `toExtension`. Likewise `Q` represents B[C] → C and `E` represents A[C] → C.
  `P.Cotangent` is I/I², and `P.cotangentComplex` is the differential.
  Mathlib's degree-zero module `P.CotangentSpace` is B ⊗ Ω[A[B]/A].
  `Generators.cotangentSpaceBasis` identifies this canonically with the free B-module
  on d[b]; `cotangentSpaceBasis_repr_one_tmul` gives exactly the formal-partial-
  derivative formula in the node. This is the canonical complex from the smooth-ring
  dependency's mathlib_match, not another cotangent complex.
- H_1(L_{B/A}), H_1(L_{C/A}), H_1(L_{C/B}) are `H1Cotangent A B`,
  `H1Cotangent A C`, `H1Cotangent B C`. These are the kernels of the preceding
  canonical differentials. `h1Cotangentι` is their inclusion into I/I².
- The base-changed two-term complex uses `P.cotangentComplex.baseChange C`.
  Its kernel is the local alias `K`. Mathlib writes C ⊗_B I/I² and C ⊗_B P.CotangentSpace;
  the node writes I/I² ⊗_B C and the corresponding free differential module.
  Tensor symmetry and the canonical differential basis identify these as precisely
  the same C-linear complex. No flatness is assumed or used to identify these terms.
- Map (a), including landing in the kernel: the existential `u : K →ₗ[C] H1Cotangent A C`
  satisfies `E.h1Cotangentι (u x) = f.liftBaseChange C x.val` for EVERY x in K.
  Here `f` is `Extension.Cotangent.map` for `Generators.defaultHom` between the canonical
  A-presentations. For canonical generators the chosen section is X, so this
  presentation map is [b] ↦ [algebraMap B C b], exactly φ_sharp, and its conormal map
  sends the class of g to the class of φ_sharp(g). `liftBaseChange` sends c ⊗ q to c • f(q).
  Injectivity of `h1Cotangentι` uniquely determines u. Its stated codomain asserts
  the required kernel landing for arbitrary base-changed cycles, not only tensors of
  cycles before base change.
- Map (b) is `v := H1Cotangent.map A B C C`, already defined with the required kernel
  codomain. Its canonical presentation map is A[C] → B[C], mapping coefficients by
  A → B and [c] to [c]. For canonical generators this follows from `self.σ' = X`
  and `Generators.defaultHom`. Thus this is the node's v, including well-definedness.
- Map (c), w, is `KaehlerDifferential.mapBaseChange A B C`, whose `mapBaseChange_tmul`
  and `map_D` signatures send c ⊗ db to c • d(algebraMap B C b).
  z is `KaehlerDifferential.map A B C C`, which sends dc to dc in Ω[C/B].
- The connecting C-linear map is the existing `H1Cotangent.δ A B C`, defined via the
  module snake lemma in `Algebra.Generators.H1Cotangent.δ`. Using this canonical map
  is more specific than existentially choosing an unspecified exact-sequence map.
  Its required explicit formula is asserted for every g in the kernel of B[C] → C
  and every h whose conormal class is `Extension.Cotangent.mk g`.
  The expression `∑ α ∈ g.val.support, (α.prod (fun c n ↦ c ^ n)) ⊗ₜ[B]
  D A B (MvPolynomial.coeff α g.val)` is precisely the coefficient formula:
  `α.prod (fun c n ↦ c ^ n)` is γ_{C/B}([c]^α), and `MvPolynomial.coeff α g.val`
  is b_α. The sum is over polynomial support. Zero coefficients outside support
  contribute zero. `D A B` is the universal derivation.
- Exactness at each internal term is stated separately as `Function.Exact u v`,
  `Function.Exact v δ`, `Function.Exact δ w`, and `Function.Exact w z`.
  `Function.Surjective z` states exactness at Ω[C/B] followed by zero.
  There is no asserted injectivity at the first term, as the node does not assert it.
- The natural comparison is the existential C-linear `t : C ⊗[B] H1Cotangent A B →ₗ[C] K`.
  Its equation `(t (c ⊗ₜ[B] h)).val = c ⊗ₜ[B] P.h1Cotangentι h` for every c and h
  uniquely specifies the canonical comparison on pure tensors; the codomain asserts
  well-defined kernel landing. Under tensor symmetry this is the node's h ⊗ c ↦ h ⊗ c.
- The implication's antecedent is `IsZero` of `CategoryTheory.Tor'` in degrees 1 AND 2,
  evaluated on Ω[B/A] and C in that order, deriving the first tensor factor as required.
  Mathlib's monoidal ModuleCat instance insists that the scalar ring and modules have
  the same universe, so the ring B and both modules are transported by ULift into
  `max u v w`. Scalar action is through `ULift.down`. `ULift.moduleEquiv` and the
  ULift ring equivalence canonically identify these Tor groups with Tor^B(Ω[B/A], C).
  These lifts impose no smallness restrictions or added assumptions.
  The consequent `Function.Bijective t` says this very natural C-linear map is an
  isomorphism, not merely that some unrelated isomorphism exists.

Dependency declarations read and used:

- `def-weil-pbc-smooth-ring-map`: mathlib_match `Algebra.Smooth`,
  `Mathlib.RingTheory.Smooth.Basic`. Its full class signature and its FormallySmooth
  fields were read. No smoothness hypothesis belongs to this item. Its recorded match
  explicitly points to `Algebra.H1Cotangent` in
  `Mathlib.RingTheory.Extension.Cotangent.Basic`, which is used, together with
  `Algebra.Generators.self`, `Algebra.Extension.cotangentComplex`, `Cotangent.map`,
  and `h1Cotangentι`. The corresponding signatures and docstrings were read.
- `def-weil-pbc-kahler-differentials`: mathlib_match `KaehlerDifferential`,
  `Mathlib.RingTheory.Kaehler.Basic`, used through Ω notation and `D`; the universal
  property `linearMapEquivDerivation` and the map/mapBaseChange APIs were read.
- `def-weil-pbc-tor-modules`: mathlib_match `CategoryTheory.Tor'`,
  `Mathlib.CategoryTheory.Monoidal.Tor`, used directly in the Tor implication.
  Its definition and documentation were read: it derives tensor in the first argument.
- `Mathlib.RingTheory.Kaehler.JacobiZariski` supplies `H1Cotangent.map` and `.δ`;
  their definitions, signatures, docstrings, and the existing partial exactness lemmas
  were read. All local aliases in the theorem are expressions in these existing notions.

Edge cases checked before writing: the zero ring is allowed for each ring (no domain or
nontriviality binders); identity maps are allowed; no surjectivity or flatness of B → C
is assumed; all polynomial-variable sets may be infinite; zero polynomial representatives
have empty support and give zero in the connecting formula. No exceptional exclusion is
made when Ω[B/A] or a kernel is zero. The Tor assertion is conditional, so failure of one
vanishing does not discard or alter the unconditional exact sequence. Independent ring
universes are supported through ULift solely in the Tor expression.

Searches made:

- msearch LeanFinder: `Jacobi Zariski exact sequence first homology naive cotangent complex`.
  Returned eight hits including `Algebra.H1Cotangent.exact_map_δ`,
  `Algebra.H1Cotangent.exact_δ_mapBaseChange`, and presentation-level snake maps.
- msearch Loogle: `Algebra.H1Cotangent, Function.Exact`. Returned those two exactness
  lemmas and `Algebra.H1Cotangent.exact_liftBaseChange_map_of_flat`.
- msearch grep, RingTheory: `H1Cotangent|Jacobi.Zariski`. Found the JacobiZariski module,
  the canonical homology API, and related smooth/etale results.
- msearch LeanSearch: `The Jacobi Zariski exact sequence for naive cotangent complex
  homology with Tor vanishing`. Service returned Internal Server Error; recorded as
  unavailable, without a mathematical verdict.
- Direct rg in WeilConjectures and lean/Sheaf for `jacobi|Jacobi|H1Cotangent` found
  uses of H1Cotangent and unrelated geometric Jacobians, no full theorem. Search for the
  exact node id in WeilConjectures returned no match.
- Direct rg for the chosen full declaration name across Mathlib, WeilConjectures,
  lean/Sheaf and dag/lean_names_upstream.json returned no match.

None of the existing declarations states the whole node: the existing theorem extending
exactness to the left assumes B-flatness of C, and the Mathlib module explicitly lists
replacement by the two Tor vanishings as TODO. Hence an existing:true record would lose
clauses or add hypotheses. The statement reuses all available canonical maps and objects.
No STATEMENT-DISPUTED issue or node fault found.

Validation: scompile server compilation passed (88 lines, 1.8 s), exit code 0, no warnings.
The declaration docstring carries all ten proof steps of the node; no proof is supplied.

## Second reading by J1

I independently read the item JSON, its complete ten-step proof, the delivered Lean file,
and all three statement-dependency nodes. The local Stacks checkout is absent. I read
upstream `algebra.tex` at
https://raw.githubusercontent.com/stacks/stacks-project/master/algebra.tex : the opening
of `section-netherlander`, canonical presentation, naive cotangent differential,
`lemma-NL-homotopy`, and the complete `lemma-exact-sequence-NL` statement and proof.
The tag page https://stacks.math.columbia.edu/tag/00S2 confirms the label. The section
starts with arbitrary ring maps; there is no ambient field, characteristic, finiteness,
Noetherian, or flatness assumption. The explicit connecting formula is the node's
expansion of the source's omitted map construction; Mathlib's `δ_eq_δAux` confirms it.

Object, hypothesis, and conclusion inventory, matched item by item:

1. Objects A, B, C are arbitrary commutative rings with maps A → B → C and the composite
   A → C. Lean: `(A : Type u) (B : Type v) (C : Type w)`, three `[CommRing]` instances,
   `[Algebra A B] [Algebra B C] [Algebra A C] [IsScalarTower A B C]`.
   Verdict: exact. Algebra structures encode the ring homomorphisms; the tower imposes
   only the specified composite. There are no other global hypotheses.
2. Canonical presentations A[B], B[C], A[C], their kernels, conormal modules, and
   differentials. Lean: `P`, `Q`, `E` are `Generators.self ... |>.toExtension`;
   `Extension.Cotangent`, `cotangentComplex`, `CotangentSpace`.
   Verdict: exact through the canonical differential basis. I read `Generators.self`
   (Generators.lean:171), `toExtension`, `cotangentComplex` (Cotangent/Basic.lean:61),
   and `cotangentSpaceBasis_repr_one_tmul` (:455). The latter evaluates formal partial
   derivatives at the generators, giving exactly the node's direct-sum differential.
   Using the basis and tensor symmetry changes coordinates, not the complex.
3. Degree-one homologies are the kernels of those differentials. Lean:
   `H1Cotangent A B`, `H1Cotangent A C`, `H1Cotangent B C`, with inclusions
   `h1Cotangentι`. Verdict: exact. I read the protected kernel definition (:339),
   the inclusion (:366), and the canonical abbreviation (:561). No smoothness is
   assumed merely because the dependency node also defines smooth ring maps.
4. Base-changed complex and its kernel. Lean:
   `K := (P.cotangentComplex.baseChange C).ker`.
   Verdict: exact, with C on the left of each tensor. This kernel includes arbitrary
   cycles after tensoring, not only base changes of cycles before tensoring.
5. Map u and its well-defined kernel landing. Lean: existential C-linear `u` together
   with `∀ x : K, E.h1Cotangentι (u x) = f.liftBaseChange C x.val`, where `f` is
   `Extension.Cotangent.map` for the canonical `Generators.defaultHom`.
   Verdict: exact. I read `defaultHom` (:468), `Hom.toAlgHom_X`, and `Cotangent.map`
   (Extension/Basic.lean:465) and its representative equation. Since `self.σ' = X`,
   the presentation map sends [b] to [algebraMap B C b]. The inclusion is injective,
   so this equation specifies the very map in the node, including its values on every
   base-changed cycle. Existential packaging merely supplies the restricted map.
6. Map v and its kernel landing. Lean: `v := H1Cotangent.map A B C C`.
   Verdict: exact. I read its definition (Cotangent/Basic.lean:564) through
   `Extension.H1Cotangent.map` (:381): it restricts the conormal map to the kernels.
   The coefficient map is A → B and the variable map fixes [c], as required.
7. Differential modules and maps w, z. Lean: Ω notation and `D A B`,
   `w := KaehlerDifferential.mapBaseChange A B C`,
   `z := KaehlerDifferential.map A B C C`.
   Verdict: exact. I read `KaehlerDifferential` (Kaehler/Basic.lean:153), `D` (:198),
   the universal property `linearMapEquivDerivation` (:327), `map` (:658), `map_D`
   (:668), and `mapBaseChange_tmul` (:723). They give the stated values on dc and c ⊗ db.
8. C-linear connecting map and its coefficient formula for every representative.
   Lean: `δ := H1Cotangent.δ A B C`, and the quantified equation for `g : Q.ker`
   and `h : H1Cotangent B C` whenever `Q.h1Cotangentι h = Extension.Cotangent.mk g`.
   Verdict: exact, with the required positive sign. I read the snake definition
   `Generators.H1Cotangent.δ`, `δ_eq`, `δAux`, `δAux_monomial`, `δ_eq_δAux`, and the
   global δ definition (JacobiZariski.lean:541). The finite support sum uses the actual
   B-coefficients of g. `α.prod (fun c n ↦ c ^ n)` is evaluation of the coefficient-one
   monomial in C. Every conormal class has an ideal representative (`mk_surjective`),
   so the representative quantification omits no h; different representatives have
   the same stated value. The existing δ already has precisely the C-linear codomain.
9. Exactness of the full sequence ending in zero. Lean: `Function.Exact u v`,
   `Function.Exact v δ`, `Function.Exact δ w`, `Function.Exact w z`,
   `Function.Surjective z`. Verdict: all internal positions and the terminal position
   match. There is no initial-zero/injectivity clause in the node, hence none is needed.
10. Natural kernel comparison, defined without Tor assumptions. Lean: existential
    C-linear `t : C ⊗[B] H1Cotangent A B →ₗ[C] K` with
    `(t (c ⊗ₜ[B] h)).val = c ⊗ₜ[B] P.h1Cotangentι h` for every c and h.
    Verdict: exact under tensor symmetry. Pure tensors generate, so this equation and
    the kernel inclusion specify the canonical comparison uniquely.
11. Conditional isomorphism when both Tor groups vanish. Lean: the conjunction of
    `IsZero` for `Tor' ... 1` and `Tor' ... 2` implies `Function.Bijective t`.
    Verdict: exact. I read Monoidal/Tor.lean:50: the first module, Ω[B/A], is resolved,
    and the second is C, as in `def-weil-pbc-tor-modules`. `ModuleCat` monoidal tensor
    uses the ring's universe. ULift raises B, Ω[B/A], and C to `max u v w`; its actions
    are through `down` (Algebra/Module/ULift.lean), and `moduleEquiv` identifies the
    underlying modules. The lifted ring is isomorphic to B. Lifting a free/projective
    resolution and its tensor complex therefore computes the same Tor groups, so this
    adds no hypothesis. Bijectivity of this C-linear comparison is precisely that it
    is an isomorphism. The implication affects only this last clause; exactness is
    unconditional.

Dependency check (H4/H12/H13): the smooth-ring-map node's Mathlib match explicitly
records the canonical `Algebra.H1Cotangent` API as well as `Algebra.Smooth`; I read
`Smooth` and `FormallySmooth` signatures and did not add either instance. The
Kähler-differential dependency matches the universal derivation above. The Tor
 dependency matches `CategoryTheory.Tor'` exactly. All local lets denote existing
objects/maps; there is no new notion or private copy. No new definition nodes or
 dependency modules were delivered, and no statement correction was necessary.

Edge cases: the zero rings, identity maps, and zero differential/homology modules are
allowed; there is no `Nontrivial`, domain, flatness, or surjectivity binder on the ring
maps. Infinite variable sets are covered by canonical multivariate polynomials. The
zero polynomial has empty support, so the coefficient formula gives zero. Empty
monomial support evaluates to one, giving the correct constant-coefficient formula.
The zero conormal class is covered by all its representatives. The two relevant Tor
degrees are literally 1 and 2; no n-variable edge case is present. Every characteristic
and three independent ring universes are admitted. There is no scheme or index-family
binder, so an empty scheme or an externally chosen empty presentation is not a case
excluded by this node's canonical-presentation formulation.

Independent searches (using different wording from the worker):

- LeanFinder via msearch: `kernel tensor change of scalars cotangent homology
  transitivity Tor`. Eight hits: cotangent-complex base-change identifications,
  `Extension.tensorCotangent`, and presentation comparison maps; no full theorem.
- Loogle via msearch: `Algebra.H1Cotangent.δ`. Four hits: δ, the two adjacent exactness
  lemmas, and `cotangentComplex_comp_h1CotangentEquivCotangent`; none gives the left
  base-changed kernel plus the Tor implication.
- LeanSearch via msearch: `Homology of the tensor product of a two term complex when
  Tor one and Tor two of its cokernel vanish`. Internal Server Error, recorded
  unavailable without a mathematical verdict.
- msearch grep: `δAux|exact_liftBaseChange_map_of_flat|cotangentComplex.baseChange`.
  Nine hits in cotangent, JacobiZariski, and etale modules; no full-node match.
- Direct rg across WeilConjectures and lean/Sheaf for `H1Cotangent|cotangentComplex|
  [Jj]acobi.*[Zz]ariski|transitivity.*cotangent`, and in the upstream declaration index
  for the item id and chosen theorem name. The source has smoothness-local uses; the
  project has other criteria and downstream uses, no existing full sequence theorem.
  Mathlib's JacobiZariski header explicitly leaves the Tor generalization as TODO,
  and its left-extension theorem assumes flatness. An existing:true record would
  discard clauses or strengthen hypotheses.

Mismatches repaired: the node's `lean.statement` was whitespace-normalized, not
verbatim. I replaced only that metadata with the exact multiline signature preceding
`:= by`. The ten-step proof docstring already described the correct mathematics;
I replaced its generic closing dependency list with the actual DAG ids indexed by
step, making the proof handoff directly usable. No mathematical signature, statement,
dependency, or proof was changed. All declarations and universes are explicitly bound;
all lines are at most 100 characters. There are no definitions and just the main
named theorem with proof `by sorry`, with source and blueprint docstrings.
