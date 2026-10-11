## Worker report

The module `Sheaf.RingTheory.EquationCountFibreDimensionFlat` states
`MvPolynomial.exists_flat_away_of_fibre_dimension_eq`, with its sole proof `sorry`.
No definitions, extra nodes, dependency modules, or statement corrections are needed.
The docstring gives every step of the node's natural-language proof and its dependencies.

Hypothesis and clause correspondence:

- A commutative ring R is `(R : Type u) [CommRing R]`, with its universe explicit.
- Nonnegative integers N >= c are `(N c : ℕ) (hc : c ≤ N)`; this encodes exactly the stated range, and subtraction is exact under hc.
- The c equations in N variables are `equations : Fin c → MvPolynomial (Fin N) R`.
- The ring S is the let-bound quotient `MvPolynomial (Fin N) R ⧸ Ideal.span (Set.range equations)`, with its canonical R-algebra structure.
- A prime q of S is `q : PrimeSpectrum S`, whose ideal is `q.asIdeal`.
- Its inverse-image prime p is `PrimeSpectrum.comap (algebraMap R S) q`.
- Residue fields and the fibre are those in `Ideal.ResidueField` and `Ideal.Fiber`. Mathlib orders the tensor factors as kappa(p) tensor S; the tensor commutation algebra equivalence identifies this with the node's S tensor kappa(p). It induces a homeomorphism on spectra and preserves the local topological dimension.
- The point Q is `PrimeSpectrum.preimageEquivFiber R S p ⟨q, rfl⟩`. Its full definition, read in Mathlib/RingTheory/LocalRing/ResidueField/Fiber.lean:155, is the kernel of `Algebra.TensorProduct.lift` of `Ideal.ResidueField.mapₐ` and the canonical map S -> kappa(q). Thus on pure tensors it sends lambda tensor s to bar(lambda) bar(s), exactly the node's point after the tensor-factor swap. The `rfl` proof merely supplies membership of q in the fibre over its own comap; it adds no hypothesis.
- The dimension hypothesis is `topologicalKrullDimAt Q = ((N - c : ℕ) : WithBot ℕ∞)`, the local topological dimension, not the dimension of the local ring.
- The first conclusion is `(∃ g : S, g ∉ q.asIdeal ∧ Module.Flat R (Localization.Away g))`.
- The second conclusion is `Module.Flat R (Localization.AtPrime q.asIdeal)`.
- The final conclusion is flatness of `Localization.localRingHom p.asIdeal q.asIdeal (algebraMap R S) rfl`, the exact canonical ring map R_p -> S_q. `RingHom.Flat` uses the algebra structure of this map, so it does not depend on a privately chosen localization algebra instance.

Dependency declarations used and read in full with their docstrings:

- `def-weil-pbc-localization-at-prime`: its Mathlib match supplies `Localization.AtPrime` (Mathlib.RingTheory.Localization.AtPrime.Basic), `Ideal.ResidueField` (Mathlib.RingTheory.LocalRing.ResidueField.Ideal), and `Ideal.Fiber` (Mathlib.RingTheory.LocalRing.ResidueField.Fiber). The same modules supply `Localization.localRingHom` and `PrimeSpectrum.preimageEquivFiber`.
- `def-kun-topological-dimension-at-point`: `topologicalKrullDimAt`, imported from `WeilConjectures.Mathlib.Topology.KrullDimension`. Its body is the infimum of `topologicalKrullDim U` over opens U containing the point, exactly the recorded definition.
- `def-weil-pbc-flat-ring-map`: `Module.Flat` (Mathlib.RingTheory.Flat.Basic) and `RingHom.Flat` (Mathlib.RingTheory.RingHom.Flat).

Edge cases checked before writing: c=0 includes the empty equation list and the zero generated ideal; N=c includes zero-dimensional fibres; N=c=0 gives S canonically R. No nontriviality, Noetherianity, characteristic, or domain assumption is imposed. If S is the zero ring there is no q, so the statement is vacuous as in the node. All primes are included, including nonclosed points: Q is formed using the canonical fibre equivalence, and dimension is taken at Q as a topological point. The inequality c≤N prevents truncated subtraction from changing the integer difference. There are no implicit free variables or universes.

Sources read: local literature/stacks-project/algebra.tex is absent on this machine, so the primary Stacks pages were opened directly: [00ST](https://stacks.math.columbia.edu/tag/00ST), [00QD](https://stacks.math.columbia.edu/tag/00QD), [00SW](https://stacks.math.columbia.edu/tag/00SW), and [00HT](https://stacks.math.columbia.edu/tag/00HT). They agree with the node; no statement fault or dispute was found.

Searches for an existing statement (msearch.py, group E1 and this item):

- leanfinder: `polynomial quotient c equations fibre dimension n minus c implies flat near prime` returned eight standard-smoothness results, including Algebra.Smooth.flat and IsStandardSmoothOfRelativeDimension; none states equation-count flatness without smoothness.
- loogle: `RingHom.Flat, MvPolynomial, Localization.Away` returned no hits.
- grep: `complete.?intersection|syntomic|equation.*flat` in RingTheory returned six hits: a presentation docstring and the equational criterion for flatness, no matching statement.
- leansearch: `quotient polynomial ring by c equations flat if local fibre dimension is n minus c` was unavailable (Internal Server Error); recorded as unavailable, not evidence of absence.
- rg over WeilConjectures and lean/Sheaf: `complete.?intersection|syntomic|equation.*flat|lem-weil-pbc-equation-count-fibre-dimension-flat` found definitions of complete intersections and unrelated effective Cartier statements; no duplicate theorem.
- rg over dag/lean_names_upstream.json, WeilConjectures and lean/Sheaf: `exists_flat_away_of_fibre_dimension_eq|equation.count.*flat|fibre.dimension.*flat` found only an unrelated locally-free theorem docstring; the declaration name is fresh.

Validation: scompile.py compiled the 54-line module on the server in 2.0 seconds, exit code 0, without warnings. Delivery dry run follows; the independent second reader supplies its own reading section.


## Second reading by E1

Independent second reader: read the sandbox node, its complete proof and Lean module,
then all three statement dependency nodes and the source declarations they record.
No mismatch was found. The Lean and node record are unchanged; this section is the
only change of the second reading.

Source verification: the local Stacks checkout is absent. Read the actual current
`algebra.tex` from https://raw.githubusercontent.com/stacks/stacks-project/master/algebra.tex,
including `lemma-localize-relative-complete-intersection` (00ST),
`lemma-relative-global-complete-intersection` (00SW), and
`definition-relative-dimension` (00QD), with their preceding context. Also read
`definition-Krull` (0055), item (4), in the corresponding `topology.tex`.
Read the primary Stacks pages [00ST](https://stacks.math.columbia.edu/tag/00ST),
[00SW](https://stacks.math.columbia.edu/tag/00SW),
[00QD](https://stacks.math.columbia.edu/tag/00QD) and
[00HT](https://stacks.math.columbia.edu/tag/00HT).
The source assumes only a commutative base ring here. Finite type in 00QD follows
from the specified finite polynomial quotient; it adds no hypothesis. The node
states the flatness consequence of 00ST(3) and 00SW, with the two localization
consequences of 00HT. No correction or citer review is needed.

Object, hypothesis and conclusion checklist (each verdict: exact):

1. Commutative base ring: `(R : Type u) [CommRing R]`. No field, domain,
   Noetherianity, characteristic or nontriviality assumption is present.
2. Integers `N ≥ c ≥ 0`: `(N c : ℕ) (hc : c ≤ N)`. Natural numbers represent
   precisely these nonnegative integers; `hc` makes natural subtraction the
   intended integer difference.
3. The `c` polynomials in `N` variables: `equations : Fin c → MvPolynomial (Fin N) R`.
   The finite labels reindex the node's numbered variables and equations.
4. The specified quotient `S`: `let S := MvPolynomial (Fin N) R ⧸
   Ideal.span (Set.range equations)`. Its canonical algebra map is the one induced
   by constants and the quotient map. There is no additional algebra choice.
5. An arbitrary prime of `S`: `∀ q : PrimeSpectrum S`; its underlying prime ideal
   is `q.asIdeal`. All primes, including nonclosed ones, occur.
6. Its inverse-image prime: `let p := PrimeSpectrum.comap (algebraMap R S) q`.
   Both occurrences of `rfl` certify definitional comap equalities; neither is a
   new condition on the prime.
7. Residue fields and fibre: the codomain of `preimageEquivFiber R S p` is
   `PrimeSpectrum (p.asIdeal.Fiber S)`. Read `Ideal.Fiber` in Mathlib's
   `LocalRing/ResidueField/Fiber.lean`: it is `p.ResidueField ⊗[R] S`.
   Read `Ideal.ResidueField` in `LocalRing/ResidueField/Ideal.lean`: it is the
   residue field of `Localization.AtPrime p`. Tensor commutation identifies this
   fibre with the node's `S ⊗[R] κ(p)`, inducing a spectrum homeomorphism.
8. The kernel point: `let Q := PrimeSpectrum.preimageEquivFiber R S p ⟨q, rfl⟩`.
   Opened its body in `Fiber.lean`: `toFun` is the kernel of the tensor-product
   lift of `Ideal.ResidueField.mapₐ` and `IsScalarTower.toAlgHom`. Opened the
   residue-field map as well: it is induced by `Localization.localRingHom`.
   Thus the map sends `λ ⊗ s` to the product of the canonical images of `λ` and
   `s` in `κ(q)`, exactly the node's map after tensor commutation.
9. The sole dimension hypothesis: `topologicalKrullDimAt Q =
   ((N - c : ℕ) : WithBot ℕ∞)`. Opened the recorded source module
   `WeilConjectures.Mathlib.Topology.KrullDimension`: the definition is
   `⨅ (U : Opens X) (_ : x ∈ U), topologicalKrullDim U` with only a topological
   space assumed. The infimum is the minimum in this well-ordered dimension
   range. This is the topological dimension at the point required by 0055 and
   00QD, not the dimension of its local ring. Tensor commutation preserves it.
10. Existence of a principal neighbourhood: `∃ g : S, g ∉ q.asIdeal ∧
    Module.Flat R (Localization.Away g)`. Exactly one `g` is chosen after `q`
    and the dimension condition, and it lies outside that prime.
11. Flatness of the prime localization over `R`:
    `Module.Flat R (Localization.AtPrime q.asIdeal)`. The scalar action is the
    canonical composite through `S`, as required.
12. Flatness of the local ring map:
    `(Localization.localRingHom p.asIdeal q.asIdeal (algebraMap R S) rfl).Flat`.
    Opened `localRingHom` in `Localization/AtPrime/Basic.lean`: it is the
    induced map `R_p →+* S_q`. Opened `RingHom.Flat`: flatness is with respect
    to this map's `toAlgebra`, exactly the node's conclusion.
13. Dependency use and flatness meaning: localization and fibre use the
    declarations of `def-weil-pbc-localization-at-prime`; local dimension uses
    the recorded declaration of `def-kun-topological-dimension-at-point`;
    flatness uses `Module.Flat` and `RingHom.Flat` of
    `def-weil-pbc-flat-ring-map`. Read `Module.Flat` and its arbitrary-module
    tensor-injectivity theorem in `Flat/Basic.lean`. Its finite testing
    definition is equivalent to the node's injectivity condition without any
    restriction on the universes of test modules. No private definition occurs.

Edge cases: `c = 0` is the empty equation family and zero generated ideal;
`N = c` means dimension zero; `N = c = 0` is the polynomial-free quotient,
canonically `R`. The zero base ring or zero quotient has empty prime spectrum,
so the assertion is vacuous, without excluding those rings. A fibre containing
`Q` is nonempty automatically. Infinite or bottom dimensions are covered by the
ambient dimension type but cannot satisfy the finite dimension equality. All
characteristics are permitted. `u` is arbitrary and the constructed quotient,
residue fields and localizations require no independent universe choice. No
variable or universe is unbound.

Independent duplicate searches, using different wording from the worker:

- `msearch.py ... leanfinder "flatness of finitely presented algebra at a prime
  with expected relative dimension and given generators relations"`: eight
  hits, including `Algebra.Smooth.flat`, smooth Noetherian descent and local
  criteria for flatness. None gives the expected-dimension implication without
  an additional smoothness or flatness hypothesis.
- `msearch.py ... loogle "Module.Flat, MvPolynomial"`: zero hits.
- `msearch.py ... leansearch "A finite presentation with as many equations as
  codimension is flat at a point of the fiber"`: unavailable, Internal Server
  Error. This is not evidence of absence.
- `rg -n -i` for `expected.{0,30}dimension`, `dimension.{0,40}flat`,
  `flat.{0,40}dimension`, `equations.{0,40}flat`, `flat.{0,40}equations`
  over Mathlib/RingTheory, all of WeilConjectures, and project lean/Sheaf:
  unrelated smoothness, Cartier, descent and cohomology hits, plus the existing
  relative/global complete-intersection definitions. Opened both project
  definition modules; neither states this flatness theorem.
- `rg` for the full proposed declaration in Mathlib, WeilConjectures,
  project lean/Sheaf and `dag/lean_names_upstream.json`: no hits; name is fresh.

H5/H6/H8/H9: no definitions, hollow or otherwise, occur; the sole theorem has
proof `sorry`. Its docstring follows all three node proof steps, including the
extra-variable localization presentation, both fibre-dimension bounds,
relative-complete-intersection flatness, tensor-injectivity transitivity, and
both localizations, naming their dependency nodes. Header, source places,
blueprint tags, namespace, topic and imports checked. Each import supplies
objects used by the statement. Every line is at most 100 characters.
A literal comparison confirms `lean.statement` equals the signature in the
module verbatim. No new nodes, dependency modules or statement changes occur.

Second-reader validation: `scompile.py` compiled the unchanged 54-line module
on the server in 1.9 seconds, exit code 0, with no warnings.
