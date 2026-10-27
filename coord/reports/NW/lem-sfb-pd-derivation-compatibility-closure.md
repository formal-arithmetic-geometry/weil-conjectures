## Worker report

The module `Sheaf.RingTheory.PDDerivationCompatibilityClosure` defines
`GradedAlgebra.pdDerivationCompatibilityLocus` by an actual set comprehension and states
`GradedAlgebra.pdDerivationCompatibilityLocus_closure`, with its entire proof `sorry`.
This is a stage-2 delivery, preserving the accepted stage-1 split and all node fields
except `lean`. The inherited stage-1 live-wins refusal is resolved by the stage-handoff
instruction in `coord/brief-stage2.md` §0: the current node has no Lean record and is
in the stage-2 queue. There is no released repair note for this item.

Hypothesis and clause correspondence:

- The commutative base ring S is `R : Type u` with `[CommRing R]`; the associative
  unital algebra is `A : Type v` with `[Ring A] [Algebra R A]`. The two universes are
  independent. `𝒜 : ℕ → Submodule R A` with `[GradedAlgebra 𝒜]` gives the actual
  internal nonnegative direct-sum grading, unit and scalar degree zero, and graded
  multiplication. `[IsStrictlyGradedCommutative 𝒜]` supplies the signed commutation
  rule and the independent odd-square-zero axiom.
- The graded divided powers are `γ : GradedDividedPowers 𝒜`, using the dependency's
  exact seven-axiom structure. Its inherited `DividedPowers.dpow_zero` gives γ_0=1
  on the positive even ideal. No new divided-power operations are defined.
- `D : A →ₗ[R] A` is the S-linear extension to finite sums. This is equivalent to
  giving compatible component maps: every element is uniquely a finite homogeneous
  sum under `GradedAlgebra`. `hdegree` puts `D x` in
  `integerComponent 𝒜 ((i : ℤ) - 1)` for each `x ∈ 𝒜 i`. In particular, D kills
  degree zero, since `integerComponent` is bottom in negative degrees. Integer
  subtraction avoids the erroneous truncated-natural-degree-zero condition.
- `hleibniz` quantifies over both homogeneous degrees and both elements and states
  `D (x*y) = D x*y + (-1:A)^i * (x*D y)`. Associativity gives exactly the node's
  signed Leibniz rule. There is no condition on D squared and no freeness assumption.
- The set C_D is represented in `evenSubalgebra 𝒜`, the existing actual subalgebra
  of A. Its defining membership requires `x ∈ positiveEvenIdeal 𝒜` and, for every
  `n : ℕ` with `0 < n`,
  `D (γ.dpow n x : A) = D (x : A) * (γ.dpow (n-1) x : A)`.
  This is precisely the node's positive even locus, including nonhomogeneous x.
- The first conjunction member is membership of zero in that locus.
- The second quantifies over x,y in the even subalgebra, assumes membership of both,
  and concludes membership of `x+y`.
- The third quantifies over arbitrary a,x in the even subalgebra, assumes only
  membership of x, and concludes membership of `a*x`. It does not require D(a)=0.
- The fourth quantifies over `m : ℕ` with `0 < m` and x in the locus and concludes
  membership of `γ.dpow m x`. It includes m=1 and excludes m=0 as required.
- The fifth quantifies over arbitrary `i j : ℕ` and `u v : A` in degrees `2*i+1`
  and `2*j+1`. These degrees parametrize every nonnegative odd degree. It concludes
  `∃ z : evenSubalgebra 𝒜, (z : A) = u*v ∧ z ∈ C_D`. This merely packages the
  same product inside the existing subtype; the underlying value fixes z uniquely.
  It imposes no additional hypothesis or chosen map. Membership includes positivity.

Dependency declarations read and used:

- `Sheaf.RingTheory.NonnegativeStrictGradedAlgebra`:
  `GradedAlgebra.IsStrictlyGradedCommutative`, `integerComponent`, `evenPart`,
  `positiveEvenPart`, `evenSubalgebra`, `evenSubalgebraCommRing`, `positiveEvenIdeal`.
  Their full definitions and the supporting `parity_properties` signature and proof
  docstring were read. The imported Mathlib `GradedAlgebra` supplies the base grading.
- `Sheaf.RingTheory.GradedDividedPowers`:
  `GradedAlgebra.GradedDividedPowers`, whose complete structure and docstring were read.
  Its inherited `DividedPowers` fields and their exact signatures were also read in
  `Mathlib.RingTheory.DividedPowers.Basic`.
- Both statement dependencies are also all proof dependencies; both are public
  imports. No dependency repair or additional DAG node is necessary. The set helper
  is part of this item's explicitly introduced locus, recorded in `lean.declarations`.

Source: read `literature/stacks-project/dpa.tex`, section-tate (09PF), all seven
axioms of definition-divided-powers-graded (09PG), the observation identifying the
ordinary divided powers on the positive even ideal, and lemma-get-derivation (09PS),
whose proof explicitly allows the lifted operator to have nonzero square. The theorem
docstring reproduces all five steps of the accepted node proof, including the integer
coefficient identity for iteration and the characteristic-two odd-square argument.

Edge cases checked before stating: zero ring; grading concentrated in degree zero
(positive even part then zero); D=0; homogeneous degree zero (D=0 there, not merely
preservation of degree zero); n=1 (γ_0=1); m=1; multiplication by degree-zero and
nonhomogeneous even elements; odd degree one; characteristic two (odd squares vanish
by the separate strictness axiom); arbitrary characteristic without division or integer
cancellation in A. No nontriviality, invertibility, characteristic, finite-generation,
freeness, or differential-square-zero restrictions are present. There is no statement
correction and no STATEMENT-DISPUTED fault.

Searches for an existing exact declaration, on 2026-10-24:

- `msearch.py leanfinder`, query: "The divided power compatibility locus of a degree
  minus one odd derivation is closed under addition, even multiplication and divided
  powers and contains odd products". Eight hits include `DividedPowers`, its rational
  and square-zero constructions and `DividedPowers.dpow_add'`; none concerns signed
  derivations or this locus.
- `msearch.py loogle`, query: `"DividedPowers", "Derivation"`. Zero hits.
- `msearch.py grep`, query:
  `divided.?power.*derivation|derivation.*divided.?power|graded.*derivation`. Zero hits.
- `msearch.py leansearch`, query: "Divided power compatibility of an odd derivation
  is stable under sums, even scalar multiples and iterated divided powers". Eight
  hits include `dpow_smul`, `dpow_mul`, `dpow_sum'`, `dpow_comp_from_gens` and
  `DPMorphism.dpow_comp`. Ordinary divided-power axioms or multiplicative ring-map
  identities do not state compatibility for the signed linear operator D.
- `rg` over both `lean/Sheaf` and `lean/WeilConjectures`, and the upstream-name
  inventory, for `pd.derivation|derivation.compatibility.locus|compatibility.closure|`
  `odd.derivation|divided.power.*derivation|derivation.*divided.power`: no matches.
  Search for this item's id in `lean/WeilConjectures` also gave no matches.

Validation: `scompile.py NW lem-sfb-pd-derivation-compatibility-closure` compiled the
file as both sandbox and library module against the published live library, including
the dependency overlay. No errors or unexpected warnings. The file explicitly sets
`autoImplicit false`, binds every universe and variable, and has no lines over 100
characters. Only the named closure theorem postpones a proof; the locus has real data.

## Second reading by NW

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
