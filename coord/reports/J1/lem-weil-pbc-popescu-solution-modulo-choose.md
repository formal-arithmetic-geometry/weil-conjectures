## Worker report

The module `Sheaf.RingTheory.PopescuSolutionModuloChoose` states
`Algebra.exists_popescu_admissible_differential_basis`, with `sorry` as its only proof.
It imports the new predicate from `Sheaf.RingTheory.PopescuAdmissibleSubalgebra`.
No result is proved. The theorem docstring contains all fifteen DAG proof steps and
all their dependency IDs. No statement correction or disputed statement was needed.

The notation is local syntax, not a second definition: `L[q]` is
`Localization.AtPrime q`, `J[q]` is the extension of `q` to `L[q]`,
`B[q, n]` is `L[q] ⧸ J[q] ^ n`, `π[q, n]` is the composite of the
localization map and the quotient map, and `m[q, n]` is `J[q]` mapped
into that quotient. The equality `(q L)^n = q^n L` identifies this
quotient with the node's displayed quotient. For `n ≥ 1` this quotient
is local with the displayed maximal ideal; no extra hypothesis asserts this.

Every hypothesis and clause is rendered as follows:

- The base field is `(k : Type u) [Field k]`; positive characteristic is
  `(p : ℕ) [CharP k p] (hp : 0 < p)`.
- The Noetherian k-algebra is `(Λ : Type v) [CommRing Λ] [Algebra k Λ]
  [IsNoetherianRing Λ]`. Geometric regularity is
  `(hreg : Algebra.IsGeometricallyRegular k Λ)`.
- The prime is `(q : Ideal Λ) [q.IsPrime]`; the integer is `(n : ℕ) (hn : 1 ≤ n)`.
  Both field and ring universes are explicitly bound and independent.
- The localization, truncated local ring, and maximal ideal are the local
  syntax explained above. `q.ResidueField` is the recorded κ(q).
- The four admissibility conditions are the fully written predicate
  `Subalgebra.IsPopescuAdmissible`: `IsArtinianRing A`, `Algebra.EssFiniteType k A`,
  an existential `IsLocalRing A`, flatness of the actual subalgebra inclusion
  `A.val.toRingHom.Flat`, and equality of the extended maximal ideal with `m`.
  Mathlib's `EssFiniteType` means a localization of a finite type algebra;
  `essFiniteType_iff_exists_subalgebra` and its localization instances establish
  the equivalence with the presentation described in the node.
- The given admissible subalgebra is `(A₀ : Subalgebra k B[q, n])`
  with `(hA₀ : A₀.IsPopescuAdmissible m[q, n])`.
- The enlargement is existential `A : Subalgebra k B[q, n]` with `A₀ ≤ A`
  and `A.IsPopescuAdmissible m[q, n]`. Its local structure is bound explicitly
  so its residue field and maximal ideal are available to elaboration.
- The parenthetical maximal-ideal contraction claim is explicitly
  `IsLocalRing.maximalIdeal A = Ideal.comap A.val.toRingHom m[q, n]`.
- `F` is the actual `IsLocalRing.ResidueField A`, the quotient by that maximal
  ideal. An injective k-algebra map `ι : F →ₐ[k] q.ResidueField` identifies it
  with a subfield containing k. The universal compatibility equation for
  `a : A` and `x : L[q]` with equal images in `B[q, n]` ensures this is the
  canonical inclusion of residue fields, rather than an unrelated embedding.
- `t r : ℕ` and `xs : Fin t → Λ`, `ys : Fin r → Λ` encode the two finite lists.
  All `ys i ∈ q` is required. Thus `t,r ≥ 0` and every listed element has
  exactly the carrier specified by the node.
- Clause (a) is expressed by witnesses `a : Fin t → A` and `a' : Fin r → A`
  with `(a j : B[q, n]) = π[q, n] (xs j)` and the analogous equality for `ys`.
  Their residues are consequently elements of F, and compatibility with ι
  identifies them with the residues of the original Λ elements in κ(q).
- Clause (b) is an actual `Module.Basis (Fin t) F (KaehlerDifferential k F)`
  whose j-th vector equals `KaehlerDifferential.D k F (IsLocalRing.residue A (a j))`.
  Thus the specified differentials themselves form a basis; it is not merely
  an assertion that some basis exists.
- Clause (c) is
  `Ideal.span (Set.range (fun i => algebraMap Λ L[q] (ys i))) = J[q]`.

Dependency declarations read and used:

- `Mathlib.RingTheory.Noetherian.Defs`: `IsNoetherianRing` and its ideal-FG meaning.
- `Sheaf.RingTheory.GRing`: `Algebra.IsGeometricallyRegular`, including its
  Noetherian condition and finite purely inseparable test extensions.
- `Mathlib.RingTheory.Localization.AtPrime.Basic`: `Localization.AtPrime`;
  `Mathlib.RingTheory.LocalRing.ResidueField.Ideal`: `Ideal.ResidueField`.
  The recorded third clause `Ideal.Fiber` is not involved in this item.
- `Mathlib.RingTheory.RingHom.Flat`: `RingHom.Flat`, which uses `Module.Flat`
  with exactly the algebra structure supplied by the ring map.
- `Mathlib.RingTheory.Kaehler.Basic`: `KaehlerDifferential` and `KaehlerDifferential.D`.
- `Mathlib.RingTheory.EssentialFiniteness`: `Algebra.EssFiniteType`, the
  `mathlib_match` of `def-weil-pbc-essentially-finite-type-algebra`, used by the new node.
- `Mathlib.RingTheory.Artinian.Ring`: `IsArtinianRing`; Mathlib local rings,
  maximal ideals, residue fields, subalgebras and bases provide the other basic objects.

Edge cases checked before writing: `n = 1` is permitted and the quotient is the
residue field; the second family then maps to zero, although it must still
span the localized prime ideal. `q = 0` for a domain is permitted and its
localized ideal can be generated by the empty family (`r = 0`). `t = 0`
is permitted when Ω(F/k) is zero (for example F=k); no nonemptiness or
positive dimension is required. Λ=0 has no prime q and so contributes no
excluded case. The characteristic hypothesis excludes characteristic zero
exactly as in the node. Arbitrary residue fields and arbitrary initial
admissible subalgebras are allowed: no choice of A₀ was restricted to one
whose elements already lift from Λ. In particular the example Λ=k[x,y],
q=0, A₀=k(x/y) still requires an enlargement, not A=A₀.

Searches for an existing statement and predicate:

- `msearch.py ... leanfinder` with “flat Artinian local subalgebra of localization
  quotient choose elements whose residue differentials form a basis”: eight
  hits, including `Algebra.Generators.basisCotangentAway`,
  `Algebra.IsStandardSmooth.of_basis_kaehlerDifferential`, and smooth-locus
  facts; none states this choice with enlargement of an arbitrary A₀.
- `msearch.py ... loogle 'KaehlerDifferential.D, Basis'`: no hits, unknown
  identifier `Basis`. The actual basis constructor used is Mathlib `Module.Basis`.
- `msearch.py ... leanfinder` with “Artinian local subalgebra essentially of
  finite type with flat inclusion whose maximal ideal generates the ambient
  maximal ideal”: eight Artinian/quasi-finite facts, no admissibility predicate.
- `msearch.py ... loogle 'Subalgebra, IsArtinianRing'`: zero hits.
- `msearch.py ... leansearch` with “admissible Artinian local subalgebra flat
  essentially finite type maximal ideal generates ambient maximal ideal”:
  unavailable, Internal Server Error. This is recorded as unavailable.
- `msearch.py ... grep 'Admissible|admissible' RingTheory`: only
  `Mathlib/RingTheory/ClassGroup/Basic.lean:429`, unrelated class-group admissibility.
- `rg -n 'IsPopescuAdmissible|admissible.*(Artinian|subalgebra)|Artinian.*admissible'`
  in Mathlib, WeilConjectures, and lean/Sheaf: no hits. Searches for the item ID
  and Popescu choice names in WeilConjectures and lean/Sheaf: no hits.
- `rg -l 'admissible.*subalgebra|subalgebra.*admissible' dag/nodes`: only this
  item and `lem-weil-pbc-popescu-solution-modulo`, which uses its terminology.
  `tools/blueprint_refs.py search admissible`: 92 broad hits, no definition
  node for this admissible-subalgebra predicate.
- Essential finite type was found in Mathlib `EssentialFiniteness.lean`, and
  its existing DAG node was read; it is reused, not redefined.

The local Stacks TeX is absent on this machine. The source was read directly
at [Tag 07FH](https://stacks.math.columbia.edu/tag/07FH) and
[Tag 07FI](https://stacks.math.columbia.edu/tag/07FI). The enlargement is the
agent argument already recorded and reviewed in this item's DAG; the theorem
retains that statement, rather than reverting to the un-enlarged Stacks choice.

Validation: both modules compiled together on the server with scompile.py,
exit code 0 in 2.6 seconds and no warnings. Every universe and parameter is
explicitly bound. No local compilation or library build was run.

## New nodes

`def-weil-pbc-popescu-admissible-subalgebra` isolates exactly the four conditions
used to call A admissible in this item. Its statement allows a specified ambient
ideal m; in this item m is the maximal ideal of the truncated localization.
The definition has real data and no `sorry`. Its source is the choice of A in
the proof of Stacks 07FH. Its Mathlib and project searches are recorded above
and in `mathlib_searches`; no existing declaration combines these conditions,
and the only DAG uses are this item and its parent. It reuses the existing
flat-map and essentially-finite-type definition nodes. The item's `stmt_deps`
gains this definition node; all other original fields are unchanged.

## Second reading by J1

I independently read the item node, both delivered modules, every statement-dependency
node and the declarations below. Verdict: the Lean says exactly what the node says;
no signature, definition, node statement, or proof changes were needed. This reading
adds only this report section. There is no statement_change in the node copy and no
dependency module in the delivery.

Source reading: the local repository has no Stacks TeX. I fetched the official
`smoothing.tex` into the sandbox scratchpad from
https://raw.githubusercontent.com/stacks/stacks-project/master/smoothing.tex and read
`section-inseparable`, `lemma-solution-modulo` (07FH), and
`lemma-enlarge-solution-modulo` (07FI), including their proofs. I also opened
https://stacks.math.columbia.edu/tag/07FH and
https://stacks.math.columbia.edu/tag/07FI. The section adds no standing assumptions.
The four conditions in the choice of A in 07FH are exactly the admissibility
predicate. The node already records the necessary enlargement argument, following
07FI's transcendental and separable-after-p-power cases. This is not a new correction:
the existing node explicitly allows enlarging an arbitrary A₀. Its example
Λ=k[x,y], q=0, A₀=k(x/y) explains why requiring A=A₀ would be wrong.

My object/hypothesis/conclusion checklist and its Lean matching:

- Base field k: `(k : Type u) [Field k]`. Positive characteristic p:
  `(p : ℕ) [CharP k p] (hp : 0 < p)`. Exact; primality follows from the
  field and characteristic, so an additional primality assumption is unnecessary.
- Noetherian commutative k-algebra Λ: `(Λ : Type v) [CommRing Λ] [Algebra k Λ]`
  and `[IsNoetherianRing Λ]`. Geometric regularity:
  `(hreg : IsGeometricallyRegular k Λ)`. Exact; not smoothness or finite type.
- Prime q: `(q : Ideal Λ) [q.IsPrime]`. Integer n≥1:
  `(n : ℕ) (hn : 1 ≤ n)`. Exact; no restriction on dimension or residue field.
- Local ring Λ_q: `L[q] = Localization.AtPrime q`. Its extended ideal:
  `J[q] = Ideal.map (algebraMap Λ L[q]) q`. Truncation:
  `B[q, n] = L[q] ⧸ J[q] ^ n`. Exact because extension commutes with
  ideal powers, giving q^n Λ_q. These are notation, not duplicate definitions.
- Ambient maximal ideal q B: `m[q, n]`, the quotient-map image of J[q].
  Ambient residue field κ(q): `q.ResidueField`, definitionally the residue
  field of L[q]. Exact. For n≥1 this quotient is local with that maximal ideal;
  these facts are not extra hypotheses in Lean.
- Admissibility: `Subalgebra.IsPopescuAdmissible`. Its definition requires
  `IsArtinianRing A`, `Algebra.EssFiniteType k A`, an existential local-ring
  instance, flatness of `A.val.toRingHom`, and
  `(IsLocalRing.maximalIdeal A).map A.val.toRingHom = m`. These are exactly
  the four conditions; essentially finite type allows any multiplicative set.
- Given arbitrary admissible A₀: `(A₀ : Subalgebra k B[q, n])`
  and `(hA₀ : A₀.IsPopescuAdmissible m[q, n])`. Exact; no liftability assumed.
- Enlargement A and residue F: existential `A : Subalgebra k B[q, n]`,
  `IsLocalRing A`, `A₀ ≤ A`, and `A.IsPopescuAdmissible m[q, n]`.
  F is `IsLocalRing.ResidueField A`. Exact quantifier order, after A₀.
  The explicit local instance supplies the same proposition as the instance
  existential in admissibility; proof irrelevance prevents a second residue notion.
- Parenthetical contraction and subfield identification:
  `IsLocalRing.maximalIdeal A = Ideal.comap A.val.toRingHom m[q, n]`,
  followed by an injective `ι : F →ₐ[k] q.ResidueField`. Its universal
  compatibility equation on a:A and x:L[q] with equal quotient images
  makes ι the actual induced residue map. Exact; not an arbitrary embedding.
- Two finite lists: `t r : ℕ`, `xs : Fin t → Λ`, `ys : Fin r → Λ`, with
  `∀ i, ys i ∈ q`. Exact; Fin uses zero-based indexing without changing lists.
- Clause (a): witnesses `a : Fin t → A`, `a' : Fin r → A`, with each coerced
  element equal to `π[q, n]` of the corresponding xs or ys. Exact membership
  and no extra restriction; the residue compatibility identifies these residues.
- Clause (b): `∃ b : Module.Basis (Fin t) F (KaehlerDifferential k F)`
  with `∀ j, b j = KaehlerDifferential.D k F (IsLocalRing.residue A (a j))`.
  Exact basis of the specified differentials, not freeness alone or spanning alone.
- Clause (c): `Ideal.span (Set.range (fun i => algebraMap Λ L[q] (ys i))) = J[q]`.
  Exact generation in the localization, not merely generation in the truncation.

Dependencies were checked at their signatures and definitions, not by name alone.
`IsNoetherianRing` in Mathlib/Noetherian/Defs is Noetherian as its own module and
is equivalent to all ideals being FG. The recorded GRing module defines geometric
regularity by Noetherianity and all finite purely inseparable base changes being
regular; its test universe is max u v, so it is not vacuous. Mathlib AtPrime is
localization at primeCompl, and Ideal.ResidueField is the residue field of AtPrime.
RingHom.Flat uses Module.Flat for the inclusion's own algebra structure.
KaehlerDifferential and D have the required universal derivation, as certified by
linearMapEquivDerivation. Module.Basis is a linear equivalence to finitely supported
coordinates. EssFiniteType and essFiniteType_iff_exists_subalgebra give precisely
the finite-type localization presentation in the node. No dependency was unusable.

The new definition node def-weil-pbc-popescu-admissible-subalgebra was independently
read against the choice of A in 07FH. Its relative-to-an-ideal formulation is exactly
the stated predicate, specialized here to the ambient maximal ideal. No hollow data
or internal sorry occurs. It cites the existing flat-map and essentially-finite-type
nodes, and the item cites it. I checked its definition kind, split status, source,
empty proof/proof_deps, null mathlib_match, search records, created record, ancestor
and via, chapter/unit, lean_audit and complete Lean record against brief §5. All match.

Independent searches (different wording from the first reader):

- LeanFinder: "enlarge a flat local subring to choose generators of cotangent space
  from the original ring": eight hits, concerning algebra presentations, cotangent
  generators, standard smoothness, and Module.exists_basis_of_span_of_flat; none
  has an enlargement of an arbitrary admissible truncated-local subalgebra.
- Loogle: `KaehlerDifferential.D, Module.Basis`: ten hits, including polynomial
  differential bases and Algebra.IsStandardSmooth.iff_exists_basis_kaehlerDifferential.
  Their signatures concern presentations or standard smoothness, not this statement.
- LeanFinder: "subring of an Artin algebra with maximal ideal extension equal to
  maximal ideal and flat inclusion": eight hits on going-down, Artinian fibres,
  ideal powers, faithful flatness and localized flatness; no admissibility predicate.
- LeanSearch: "local Artinian subalgebra flat inclusion residue field differential
  basis enlargement": unavailable (Internal Server Error), not evidence of absence.
- rg on Mathlib/RingTheory, all WeilConjectures, and lean/Sheaf for
  `popescu|artinian.*subalgebra|subalgebra.*artinian`: only unrelated Gabriel-Popescu
  and the separate PopescuResolution/HenselianPairApproximation modules. Their
  notions do not duplicate this predicate or theorem. Additional admissib and
  differential_basis searches in source and project RingTheory found no match.
- DAG search for admissible subalgebra terminology found only this item and its
  parent use. `blueprint_refs.py search 'Artinian subalgebra'` found no node.
  Together with the existing essential-finite-type node, this supports one new
  combination predicate, without duplicating any component notion.

Edge cases: t=0 and r=0 are allowed by Fin 0. For zero differentials, an empty basis
is permitted; for q=0 in a domain, the localized ideal is zero and the empty span
is permitted. For n=1, ys have zero truncation image but must still generate J[q],
as required. n=0 and characteristic zero are outside the source hypotheses.
The zero ring Λ has no prime, so excluding it through q.IsPrime drops no valid
instance. Empty schemes are inapplicable to this ring statement. Independent u,v
allow arbitrary field and algebra universes, and the localization, quotient,
subalgebra and residue field carry their natural universes without extra smallness.
No nonempty family, perfect field, finite extension, or finite-type Λ was assumed.

Docstrings contain the source and blueprint IDs. The theorem docstring reproduces
all fifteen node proof steps, including their dependencies (some IDs wrap over a
line break). Each import supplies notions used by the declaration; names have no
Sheaf namespace prefix. There is exactly one named theorem with proof `sorry` and
one concrete definition. The theorem's lean.statement equals its signature verbatim;
all variables and universes are explicitly bound.

Validation: scompile.py compiled both modules together in dependency order,
exit code 0, 2.5 seconds, no warnings. No repository git command, source edit,
local build, or global build was run. No mathematical mismatch was found;
only this independent review report was appended.
