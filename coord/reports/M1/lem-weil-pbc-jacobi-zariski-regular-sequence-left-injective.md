## Worker report

The module `Sheaf.RingTheory.JacobiZariskiRegularSequenceLeftInjective` states
`Algebra.jacobiZariski_left_injective_of_regularSequence`, with one sorry and no new definitions.
The node is unchanged except for its lean record. No dependency replacement is required.

Hypotheses and clauses:

- Commutative ring maps A → B → C are `[CommRing A] [CommRing B] [CommRing C]`,
  `[Algebra A B] [Algebra B C]`; `[Algebra A C] [IsScalarTower A B C]` says that the
  A-algebra structure on C is the composite. These bind arbitrary universes u, v, w.
- The integer m ≥ 0 is `m : ℕ`; the finite regular sequence is the list
  `fs : List (MvPolynomial (Fin m) B)`, with c = fs.length. Lists record the ordered
  elements without imposing any extra condition on their length.
- Regularity is `hreg : RingTheory.Sequence.IsRegular (MvPolynomial (Fin m) B) fs`,
  including both the successive nonzerodivisor condition and nonzero final quotient.
- The B-algebra homomorphism is `β`, its surjectivity is `hβ`, and its kernel is
  `hker : RingHom.ker β.toRingHom = Ideal.ofList fs`.
- The canonical presentations A[B] → B and A[C] → C are
  `Generators.self A B` and `Generators.self A C`, with extensions P and Q.
  Their conormal modules are `P.Cotangent`, `Q.Cotangent`; the differential is
  `P.cotangentComplex`. Mathlib realizes the free module of differentials as
  `B ⊗[A[B]] Ω[A[B]/A]`, with its polynomial basis in
  `Generators.cotangentSpaceBasis`; its differential on a conormal class g is
  `1 ⊗ D g`, precisely the partial-derivative formula in that basis.
- `F := (Generators.defaultHom (Generators.self A B) (Generators.self A C)).toExtensionHom`
  is the specified φ♯. Reading `self` and `defaultHom` shows its variable assignment
  is definitionally b ↦ X (algebraMap B C b): self has val = id and section σ = X.
  Thus this is not an arbitrary choice of lifts.
- `g := (Extension.Cotangent.map F).liftBaseChange C` is the C-linear conormal map
  c ⊗ (g mod I²) ↦ c • (φ♯(g) mod I²), using Mathlib's reversed tensor-factor order.
  The tensor symmetry identifies this with the node's (I/I²) ⊗ C formula.
- `d := P.cotangentComplex.baseChange C` is δ ⊗ id under the same symmetry;
  `LinearMap.ker d` is exactly H₁(NL[B/A] ⊗ C). It is NOT replaced by
  C ⊗ H₁(L[B/A]), which need not agree without flatness.
- `∃ u : LinearMap.ker d →ₗ[C] H1Cotangent A C` together with
  `∀ x, Q.h1Cotangentι (u x) = g x.1` expresses that g carries this kernel
  into H₁(L[C/A]) and that u is its restriction. The inclusion is injective,
  so this equation determines u uniquely. `Function.Injective u` is the last clause.

Dependency declarations used and read with their docstrings/signatures:

- def-weil-pbc-mv-polynomial-ring: Mathlib.Algebra.MvPolynomial.Basic,
  `MvPolynomial` and `MvPolynomial.algHom_ext`; Mathlib.Algebra.MvPolynomial.Eval,
  `MvPolynomial.aeval`. The theorem uses MvPolynomial directly and the canonical
  presentations implemented through aeval.
- def-weil-pbc-regular-sequence: Mathlib.RingTheory.Regular.RegularSequence,
  `RingTheory.Sequence.IsRegular`.
- def-weil-pbc-smooth-ring-map: its mathlib_match is `Algebra.Smooth` in
  Mathlib.RingTheory.Smooth.Basic. The node's naive-complex and H₁ clauses are
  already given by `Algebra.Extension.cotangentComplex`,
  `Algebra.Extension.H1Cotangent`, `Algebra.H1Cotangent`, in
  Mathlib.RingTheory.Extension.Cotangent.Basic, as the dependency's match explains.
  Smoothness is not assumed here. These existing definitions supply exactly the
  relevant clauses; importing Smooth.Basic merely for its unused Smooth predicate
  would be an unused import.

Edge cases checked before writing: m = 0 is allowed (polynomial ring on Fin 0);
fs = [] is allowed (zero kernel, with nonzero quotient required by regularity).
The zero ring cannot satisfy this regularity condition, consistently with the node's
nonzero final quotient. No characteristic, Noetherianity, flatness, or ring-map
injectivity assumption is introduced. The kernel after tensoring remains correct
when C is not flat over B. All universes and variables are explicitly bound.

Source checked: the local literature/stacks-project directory is absent on this machine;
opened https://stacks.math.columbia.edu/tag/07D4 instead. Its “in particular” sequence
starts with 0 → H₁(NL[B/A] ⊗ C) → H₁(L[C/A]), exactly the conclusion here.
The four proof steps and their DAG references are carried in the theorem docstring.
No statement fault or dispute found.

Searches (msearch.py M1 and source rg/grep):

- leanfinder: “Jacobi Zariski base changed naive cotangent complex first homology map
  injective regular sequence quotient”. Eight hits: CotangentSpace.map_toComp_injective,
  submersive-presentation injectivity, Extension.h1Cotangentι_injective, smoothness
  criteria, and localization-away injectivity. None states the required theorem.
- loogle: “Algebra.H1Cotangent, Function.Injective”. Four hits: two smoothness
  criteria and two free-cotangent equivalence lemmas; no match.
- grep: “mapBaseChange|cotangentComplexBaseChange|liftBaseChange” in RingTheory/Kaehler.
  Fifteen hits; JacobiZariski only extends to the left under flatness and does not
  state this injection from the kernel of the base-changed differential.
- leansearch: “Jacobi Zariski left injectivity regular sequence quotient naive
  cotangent complex”. Service unavailable: Internal Server Error.
- rg in WeilConjectures and lean/Sheaf for jacobi/Jacobi/regular.*injective/
  cotangentComplexBaseChange: related references and smoothness statements, no match.
- grep of the exact item id in WeilConjectures: no hit.
- rg of the proposed full declaration name in dag/lean_names_upstream.json,
  Mathlib, WeilConjectures, and lean/Sheaf: no collision.

Validation: scompile.py compiled the module on the server in 1.5 seconds, exit 0,
with no errors or warnings. Delivery dry run follows; independent second reading is
left to the second reader as instructed.

## Second reading by M1

I reread the node statement and the Lean declaration item by item. The rings and
maps are rendered by `(A : Type u) (B : Type v) (C : Type w)`, commutative-ring
instances, `[Algebra A B] [Algebra B C] [Algebra A C]`, and
`[IsScalarTower A B C]`; this exactly expresses the composite A-algebra structure
on C. The integers `m,c ≥ 0` are rendered by `m : ℕ` and the implicit
`c = fs.length`; `fs : List (MvPolynomial (Fin m) B)` has the required ordered
elements. Regularity is exactly `hreg : RingTheory.Sequence.IsRegular ... fs`.
The B-algebra quotient is `β : MvPolynomial (Fin m) B →ₐ[B] C`, with
`hβ : Function.Surjective β` and
`hker : RingHom.ker β.toRingHom = Ideal.ofList fs`.

For the conclusion, `P := (Generators.self A B).toExtension` and
`Q := (Generators.self A C).toExtension` are the canonical presentations and
their `Cotangent`/`cotangentComplex` fields render the stated conormal modules
and differential. `d := P.cotangentComplex.baseChange C` has kernel exactly the
base-changed H₁ in the node. `F` is the canonical `defaultHom` and hence sends
each generator `[b]` to `[φ b]`; `g := (Extension.Cotangent.map F).liftBaseChange C`
is the displayed conormal map (with Mathlib's reversed tensor convention).
The existential linear map `u : LinearMap.ker d →ₗ[C] H1Cotangent A C`, the
equation `Q.h1Cotangentι (u x) = g x.1`, and `Function.Injective u` render,
respectively, that the map lands in H₁, is its restriction, and is injective.
Quantifier order and all hypotheses agree; no extra smoothness, flatness,
Noetherianity, characteristic, or injectivity assumptions occur.

Edge cases remain covered: `m = 0`, `fs = []`, arbitrary characteristics and
universes, and non-flat C/B. The regularity predicate excludes the zero-ring case
exactly as the source does. I searched Mathlib, `WeilConjectures/`, `lean/Sheaf/`,
and the upstream-name index (LeanSearch was unavailable; leanfinder, loogle and
grep found only related Jacobi–Zariski and cotangent lemmas). No existing exact
declaration was found.

No mismatch was found and no source or Lean text required changing. The module
compiles cleanly with `scompile.py`; its only proof placeholder is the permitted
statement `sorry`.
