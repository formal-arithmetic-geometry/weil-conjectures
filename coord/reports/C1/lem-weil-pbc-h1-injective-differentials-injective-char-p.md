## Worker report

The module `Sheaf.RingTheory.DifferentialsInjectiveOfH1CotangentInjectiveCharP`
states `Algebra.differentials_injective_of_h1Cotangent_injective_charP` with a
single `sorry` proof. It introduces no definitions or axioms. The node is unchanged
except for its `lean` record. No dependency modules or new nodes are needed.

Source checked: https://stacks.math.columbia.edu/tag/07E5, proof of the equivalence
of (3) and (4), specifically the two Jacobi–Zariski rows and their commuting square.
The local literature checkout has no stacks-project directory, so the official tag
was read directly. The node isolates the implication on injectivity from this
argument; the argument does not use regularity. Its five proof steps are reproduced
in the declaration docstring, including the nodes used in each step.

Correspondence of every hypothesis and clause:

- The characteristic is `(p : ℕ) (hp : 0 < p)`; the base field is `(k : Type u)
  [Field k] [CharP k p]`. This is exactly positive characteristic, with primality
  following from being a field rather than an extra hypothesis.
- The Noetherian local k-algebra is `(A : Type v) [CommRing A] [IsLocalRing A]
  [IsNoetherianRing A] [Algebra k A]`. No regularity or finite type is imposed.
- The maximal ideal is the canonical `IsLocalRing.maximalIdeal A`, and the residue
  field is `let K := IsLocalRing.ResidueField A`, definitionally its quotient.
  There is no independent K with an unspecified quotient map.
- The prime-field structures are `letI := ZMod.algebra k p` and the algebra on A
  induced by the composite `ZMod p → k → A`. The algebra on K and compatible
  scalar towers are supplied by the quotient/residue-field instances. This
  constructs the structures the node specifies; none are additional hypotheses.
- The differentials and universal derivation are Mathlib's
  `KaehlerDifferential` and `KaehlerDifferential.D`, as recorded by the dependency.
- `H1Cotangent k K` and `H1Cotangent A K` are the kernels for
  `(Generators.self k K).toExtension` and `(Generators.self A K).toExtension`.
  These are the canonical polynomial presentations with variables indexed by K.
- `H1Cotangent.map k A K K` is the K-linear presentation homology map. Its
  `Generators.defaultHom` sends each variable indexed by x in K to that same
  variable in A[K]: the designated section of `Generators.self` is X, and
  `algebraMap K K` is the identity. Thus this is exactly the coefficient inclusion
  of presentations in the node (and `Extension.H1Cotangent.map_eq` also ensures
  independence of the lift).
- `P := Extension.ofSurjective (Algebra.ofId A K)
  IsLocalRing.residue_surjective` has ring A and kernel m. The canonical isomorphism
  is `P.h1CotangentEquivCotangent : H1Cotangent A K ≃ₗ[K] P.Cotangent`.
  Its target is the kernel's cotangent module, m/m². The let-bound `γ` is its
  linear map composed with the preceding homology map, exactly as specified.
- `lambdaMap` uses `(TensorProduct.isBaseChange k Ω[k⁄ZMod p] K).lift` on the
  k-linear map formed by `KaehlerDifferential.map (ZMod p) (ZMod p) k A` followed
  by `ω ↦ 1 ⊗ ω`, given by `TensorProduct.mk A K Ω[A⁄ZMod p] 1`.
  Consequently it sends `x ⊗ da` to `x ⊗ d(algebraMap k A a)` and is K-linear.
  Its source is K ⊗[k] Ω[k/F_p] and its target K ⊗[A] Ω[A/F_p]. Tensor
  commutativity identifies these with the node's right-hand tensor factors;
  conjugation by these canonical isomorphisms preserves injectivity.
- The hypothesis and conclusion are precisely
  `Function.Injective γ → Function.Injective lambdaMap`.

Dependency declarations read and used:

- def-pc-field-characteristic: `CharP` in Mathlib.Algebra.CharP.Defs
  (available through Mathlib.Algebra.Algebra.ZMod).
- def-weil-pbc-noetherian-ring: `IsNoetherianRing` in
  Mathlib.RingTheory.Noetherian.Defs.
- def-weil-pbc-kahler-differentials: `KaehlerDifferential`, `D`,
  `linearMapEquivDerivation`, and `map` in Mathlib.RingTheory.Kaehler.Basic
  (available through Extension.ExtendScalars).
- def-weil-pbc-smooth-ring-map: `Algebra.H1Cotangent` in
  Mathlib.RingTheory.Extension.Cotangent.Basic. Its match explicitly records this
  notion in addition to Algebra.Smooth; smoothness is not a hypothesis here.
- lem-weil-pbc-nl-presentation-h1-functoriality:
  `Algebra.Extension.H1Cotangent.map`, `map_eq`, `map_id`, `map_comp` in
  Mathlib.RingTheory.Extension.Cotangent.Basic, through `Algebra.H1Cotangent.map`.
- lem-weil-pbc-jacobi-zariski-surjection-h1:
  `Algebra.Extension.h1CotangentEquivCotangent` in
  Mathlib.RingTheory.Extension.ExtendScalars, specialized to `ofSurjective`.

Edge cases checked: p = 0 is explicitly excluded; p = 1 and composite positive p
cannot satisfy the field characteristic hypothesis. The zero ring cannot be a
local ring in Mathlib, consistently with a local algebra having a residue field.
For A = k, m = 0 and the conclusion is the identity on residue-field differentials;
for k = F_p, the source differentials vanish. Imperfect k and nonregular local A
are allowed. Universes u and v are independent and explicit; using the canonical
quotient K does not impose a size restriction on an abstract residue field.
No formal smoothness, finite generation, separability of K/k, or nonzero
cotangent module is assumed. No statement fault or dispute was found.

Searches for an existing statement (all msearch calls recorded in searches.jsonl):

- LeanFinder: "Characteristic p local algebra residue field: injectivity of first
  cotangent homology into maximal ideal cotangent implies injectivity of base
  field differentials tensor residue field". Eight results: formal smoothness
  criteria, submersive-presentation injectivity, cotangent-space comparison, and
  inclusion of H1 into its presentation conormal module; none states this implication.
- Loogle: "Algebra.H1Cotangent.map, KaehlerDifferential.mapBaseChange".
  Zero hits for the combined query.
- Mathlib grep via msearch: "H1Cotangent|mapBaseChange" in RingTheory/Kaehler.
  Ten hits: the standard maps and exact sequences, no matching theorem.
- LeanSearch: "In positive characteristic, injectivity of residue-field first
  cotangent homology into the conormal module implies injectivity of base field
  Kahler differentials after residue-field base change". Service unavailable
  (Internal Server Error); no mathematical verdict inferred.
- rg in WeilConjectures and lean/Sheaf for the item id, H1Cotangent and mapBaseChange:
  only existing Cartier equality, field homology vanishing, and localized
  cotangent vanishing in Sheaf; no occurrence in the source project and no match.
- rg for the chosen full declaration basename in dag/lean_names_upstream.json,
  WeilConjectures, and Mathlib: no collision.

Validation: server scompile.py returned exit code 0, compiled in 1.7 seconds,
with no errors or warnings. The only theorem proof is `sorry`, as required.

## Second reading by C1

The node introduces, in order: a natural number `p` with `0 < p`; a field `k`
with `CharP k p`; a commutative ring `A` with `IsLocalRing A`,
`IsNoetherianRing A`, and `Algebra k A`; the residue field `K = A / m`; the
canonical `F_p`-algebra structures on `k`, `A`, and `K`; the canonical
presentations `k[K] → K` and `A[K] → K`; the induced `K`-linear map on their
`H1Cotangent`s; the canonical isomorphism from `H1Cotangent A K` to `m/m²`;
`γ` as their composite; and `λ` on prime-field Kähler differentials. The
conclusion is `Function.Injective γ → Function.Injective λ`.

The Lean renders these as `(p : ℕ) (hp : 0 < p)`, `[Field k] [CharP k p]`,
`[CommRing A] [IsLocalRing A] [IsNoetherianRing A] [Algebra k A]`,
`K := IsLocalRing.ResidueField A`, the two `letI` ZMod/algebra structures,
`H1Cotangent.map k A K K`, `Extension.ofSurjective ...`,
`P.h1CotangentEquivCotangent.toLinearMap.comp ...`, and the final implication.
`lambdaMap` is the canonical base-change lift and sends the stated generators;
its internal presentation is `K ⊗ Ω` while the node writes the canonically
commuted `Ω ⊗ K` factors. This is the same K-linear map under the standard
base-change tensor commutativity identification, and no extra hypothesis is
introduced. Every hypothesis and conclusion clause is present with the same
strength; the Noetherian hypothesis is retained although unused in the chase.

Edge cases checked: `p = 0` is excluded; `CharP k p` forces the positive
characteristic to be prime; zero rings are excluded by `[IsLocalRing A]` and
`[Field k]`; `A = k` gives the zero conormal case; `k = F_p` gives vanishing
source differentials; imperfect fields and nonregular local rings remain
allowed; and the explicit universes `u,v` do not impose a size restriction.

Searches were repeated with LeanFinder and Loogle for H1 cotangent/differential
injectivity, LeanSearch (service unavailable), and `rg` over Mathlib,
`WeilConjectures`, and `lean/Sheaf`; no existing declaration states this
implication. The only issue found was the tensor-factor orientation in the
first worker's explanation; the Lean base-change lift was checked directly and
left unchanged because the node's factors are canonically commuted. No node,
dependency, or statement correction was needed.

## Reviewer fix (R-hdi1100)

The characteristic binders `(p : ℕ) (hp : 0 < p) ... [CharP k p]` were replaced by the
project spelling `(p : ℕ) [Fact p.Prime] [CharP k p]`, with the binder order of J1's
`isRegularLocalRing_and_injective_h1Cotangent_of_isGeometricallyRegular` (f19521d3d),
whose γ this statement repeats verbatim; for a field the two forms are equivalent.
Checked in Lean that `lambdaMap (1 ⊗ D a) = 1 ⊗ D (algebraMap k A a)`.
