## Worker report

The module `Sheaf.AlgebraicGeometry.QuasiFiniteMorphism` defines four predicates in
`AlgebraicGeometry.Scheme.Hom`, with no proofs or sorries. The node's statement is unchanged.
The source was read at https://stacks.math.columbia.edu/tag/01TD (Definition 29.21.1),
which agrees with the three numbered clauses of the node.

Hypothesis and clause correspondence:

- An arbitrary morphism of schemes is `{X S : AlgebraicGeometry.Scheme.{u}} (f : X ⟶ S)`;
  there are no field, Noetherian, separatedness, nonemptiness, or finite-type assumptions
  on the ambient morphism.
- Clause 1: `IsQuasiFiniteAtPoint f x` quantifies over `U : X.Opens`, membership
  `hx : x ∈ U`, and `hU : IsAffineOpen U`; it then quantifies over `V : S.Opens`
  with `IsAffineOpen V`. These are precisely the two affine opens in the node.
  Their coordinate rings are the section rings; no affine presentation choices are needed.
  `e : U ≤ f ⁻¹ᵁ V` expresses `f(U) ⊆ V`. The induced coordinate-ring map is
  `(f.appLE V U e).hom`. Its `.FiniteType` is required, and its `.QuasiFiniteAt`
  is evaluated at `(hU.primeIdealOf ⟨x, hx⟩).asIdeal`, the prime corresponding to x.
- Clause 2: `IsLocallyQuasiFinite f` is `∀ x : X, IsQuasiFiniteAtPoint f x`.
- Clause 3: `IsQuasiFinite f` requires `LocallyOfFiniteType f ∧ QuasiCompact f`,
  exactly finite type under the convention dependency. For every `x : X` it requires
  `IsOpen ({f.asFiber x} : Set (f.fiber (f x)))`, precisely isolation in the fibre.
- Finite fibres: `HasFiniteFibres f` is `∀ s : S, (f ⁻¹' {s}).Finite`.
- The fibre scheme is reused, not redefined: Mathlib `Scheme.Hom.fiber f s` is
  `pullback f (S.fromSpecResidueField s)`, namely `X ×_S Spec κ(s)`.
  `Scheme.Hom.asFiber` supplies x in that fibre; `Scheme.Hom.fiberHomeo` identifies
  its underlying space with the preimage singleton.

Dependency declarations read and used:

- `def-weil-pbc-scheme-conventions` has a convention-only `lean` record, with no module
  or declaration. Its statement explicitly fixes no new notion; its record directs citers
  to Mathlib. No dependency repair is needed. Its relevant declarations are
  `AlgebraicGeometry.Scheme`, `LocallyOfFiniteType`, `QuasiCompact`, and `Scheme.Hom.fiber`.
- The single import `Mathlib.AlgebraicGeometry.Morphisms.QuasiFinite` supplies those
  notions, `IsAffineOpen`, `Scheme.Hom.appLE`, and ring-level `RingHom.QuasiFiniteAt`.
  Finite type is `RingHom.FiniteType`. The fibre declarations and docstrings were read
  in `Mathlib.AlgebraicGeometry.Fiber`, the finite-type class in
  `Mathlib.AlgebraicGeometry.Morphisms.FiniteType`, and the ring predicates in
  `Mathlib.RingTheory.RingHom.QuasiFinite` and `Mathlib.RingTheory.RingHom.FiniteType`.

Existing-definition searches:

- `msearch.py ... leanfinder "scheme morphism quasi-finite at a point locally quasi-finite
  finite type isolated fibre points"`: eight hits, principally `LocallyQuasiFinite`,
  `LocallyOfFiniteType`, and related instances; none is the complete definition.
- `msearch.py ... loogle "AlgebraicGeometry.Scheme.Hom.QuasiFiniteAt,
  AlgebraicGeometry.LocallyQuasiFinite"`: three results, `quasiFiniteAt`,
  `quasiFiniteAt_comp_iff`, and `quasiFiniteAt_iff`.
- `msearch.py ... grep "def QuasiFiniteAt|class LocallyQuasiFinite|def.*FiniteFib|def.*QuasiFinite"
  AlgebraicGeometry`: `LocallyQuasiFinite`, `Scheme.Hom.QuasiFiniteAt`, and `quasiFiniteLocus`.
- `msearch.py ... leansearch "quasi finite morphism at a point finite type isolated fibre"`:
  unavailable, Internal Server Error.
- `rg` of `QuasiFiniteAt|quasiFiniteAt|HasFiniteFib|IsQuasiFinite` in the project's
  `lean/Sheaf` and source `WeilConjectures`: only ring-level predicates, applications,
  and related lemmas. `grep -rn pqf-def-quasifinite` in `WeilConjectures`: no hits.
  The candidate full names were also searched in Mathlib, the source, `lean/Sheaf`,
  and `dag/lean_names_upstream.json`: no collisions.

Mathlib's `LocallyQuasiFinite` explicitly does not require locally finite type.
Its `Scheme.Hom.QuasiFiniteAt` tests the stalk ring map and likewise does not impose
local finite type. They therefore cannot be recorded as exact matches for clauses 1–2.
The existing ring-level predicate is used together with finite type, not copied.
The project's `Algebra.IsQuasiFiniteAtPrime` was also read: it imposes a finite-type
algebra instance and uses an open singleton in the spectrum of the fibre ring.
No new underlying notion is needed here because Mathlib provides the ring-map predicate.

Edge cases checked before writing: empty X makes the universal point and fibre conditions
vacuous, as intended; finite type in clause 3 still remains explicit. Empty fibres count as
finite. No surjectivity is imposed. Disjoint infinite unions of points illustrate why
finite fibres, local quasi-finiteness, and global quasi-finiteness must remain distinct.
The localization ℤ → ℚ illustrates why Mathlib's predicates alone are insufficient:
it is quasi-finite in Mathlib's sense but is not of finite type. An infinite algebraic
field extension has an isolated fibre point but fails both finite type and Mathlib's
residue-field finiteness condition. Nilpotents are permitted, and point isolation concerns topology,
not reducedness. `Scheme.{u}` keeps the arbitrary scheme universe explicit.

No statement dispute, correction, new node, or dependency module was needed.


## Second reading by C1

I read the sandbox node and Lean file against Stacks Tag 01TD in
`/home/ubuntu/c1-stacks-review/morphisms.tex`, lines 3523–3555. The tag-to-label
entry is `01TD,morphisms-definition-quasi-finite`. The preceding paragraph refers
to the finite-type ring definition in `algebra.tex`, lines 30232–30241 (Tag 00PL).
Neither the section nor the definition assumes a field, Noetherian schemes,
separatedness, surjectivity, or nonempty schemes. The blueprint adds finite fibres
and the scheme-theoretic fibre convention; these also appear in the node.

The complete object/hypothesis/clause list and correspondence is:

| Node item | Lean rendering | Verdict |
| --- | --- | --- |
| Arbitrary schemes X, S and morphism f | `{X S : AlgebraicGeometry.Scheme.{u}} (f : X ⟶ S)` in each definition | Exact; no extra instances. |
| Clause 1: point x of X | `(x : X)` in `IsQuasiFiniteAtPoint` | Exact. |
| Affine neighbourhood U = Spec A of x | `∃ (U : X.Opens) (hx : x ∈ U) (hU : IsAffineOpen U)` | Exact; `hU.isoSpec` identifies U with the spectrum of its section ring. |
| Affine open V = Spec R in S | `(V : S.Opens), IsAffineOpen V ∧ ...` | Exact; no assumption on an arbitrary target neighbourhood. |
| f(U) contained in V | `∃ e : U ≤ f ⁻¹ᵁ V` | Exact image-containment condition, after choosing both opens. |
| Induced ring map R → A is finite type | `(f.appLE V U e).hom.FiniteType` | Exact direction: sections on S to sections on X. |
| Ring map is quasi-finite at the prime corresponding to x | `.QuasiFiniteAt (hU.primeIdealOf ⟨x, hx⟩).asIdeal` | Exact under the preceding finite-type conjunct; see below. |
| Clause 2: quasi-finite at every point | `∀ x : X, IsQuasiFiniteAtPoint f x` | Exact; witnesses may depend on x. |
| Clause 3: finite type | `LocallyOfFiniteType f ∧ QuasiCompact f` | Exact convention, with no quasi-separatedness added. |
| Every point isolated in its fibre | `∀ x : X, IsOpen ({f.asFiber x} : Set (f.fiber (f x)))` | Exact singleton openness in the fibre topology. |
| Finite fibres at every s | `∀ s : S, (f ⁻¹' {s}).Finite` | Exact set finiteness, including empty fibres. |
| Fibre X ×_S Spec κ(s) | Existing `Scheme.Hom.fiber f s` | Exact pullback along `S.fromSpecResidueField s`; reused, not copied. |

I opened the only statement dependency, `def-weil-pbc-scheme-conventions`.
It explicitly introduces no independent notion, and its `lean` record is a
convention record with no declaration or module. Its finite-type convention is
locally finite type plus quasi-compact, precisely clause 3. I opened the actual
signatures in Mathlib: `LocallyOfFiniteType.finiteType_appLE`,
`QuasiCompact.isCompact_preimage`, `Scheme.Hom.appLE`,
`IsAffineOpen.primeIdealOf`, `Scheme.Hom.fiber`, `fiberHomeo`, and `asFiber`.
The affine coordinate prime has type `PrimeSpectrum Γ(X, U)`; `appLE` has type
`Γ(S, V) ⟶ Γ(X, U)`. The prime instance is therefore the canonical one, with no
extra hypothesis. `fiberHomeo` has type `f.fiber s ≃ₜ f ⁻¹' {s}`, and `asFiber`
is its inverse at x, so the singleton belongs to the correct fibre.

I also opened `RingHom.QuasiFiniteAt` and `Algebra.QuasiFiniteAt` in Mathlib.
They use quasi-finiteness of the localization at the chosen prime, without
finite type. `Algebra.quasiFiniteAt_iff_isOpen_singleton_fiber` in
`Mathlib/RingTheory/ZariskisMainTheorem.lean:754` explicitly assumes
`[FiniteType R S]` and identifies that predicate with isolation in the fibre.
Thus using the existing predicate together with `.FiniteType` gives precisely
the source's ring-level clause, with no strengthening. The project's
`Algebra.IsQuasiFiniteAtPrime` in `Sheaf/RingTheory/QuasiFiniteAtPrime.lean`
expresses the same ring-level notion topologically with a finite-type instance;
it is not a scheme-morphism definition and is not a dependency of this node.
The delivered definition reuses Mathlib's predicate rather than defining a
second ring-level notion.

Independent searches (different queries from the worker):

- `msearch.py C1 pqf-def-quasifinite leanfinder "scheme morphism isolated points of fibres and finite type definition"`:
  eight hits, including `LocallyQuasiFinite`, `LocallyOfFiniteType`, `IsFinite`,
  and finite/discrete-fibre consequences for finite maps. None defines these
  four notions with the source's hypotheses.
- `msearch.py C1 pqf-def-quasifinite loogle '"QuasiFiniteAt"'`:
  twelve hits, principally `Algebra.QuasiFiniteAt`, `RingHom.QuasiFiniteAt`, and
  their API; their actual declarations were opened as above.
- `msearch.py C1 pqf-def-quasifinite leansearch "scheme morphism finite type with discrete fibers quasi finite definition"`:
  unavailable (Internal Server Error); no mathematical verdict drawn from it.
- Independent `rg` searches for `finite.?fib(re|er)` and declaration keywords
  with `quasi.?finite` across Mathlib AlgebraicGeometry, the entire source
  `WeilConjectures`, and repository `lean/Sheaf` found only the Mathlib weaker
  scheme predicates, `quasiFiniteLocus`, the existing ring-level definition,
  and applications. I opened the source extension
  `WeilConjectures/Mathlib/AlgebraicGeometry/Morphisms/QuasiFinite.lean`:
  it adds results about Mathlib's predicate, no exact definition for this node.
- Full-name searches for `IsQuasiFiniteAtPoint`, `IsLocallyQuasiFinite`,
  `IsQuasiFinite`, and `HasFiniteFibres` in the source, project library, and
  `dag/lean_names_upstream.json` found no scheme-level collision.

Edge cases: empty X makes clauses 1–2 and the isolation condition vacuous;
clause 3 still requires finite type, as stated. Empty S permits only empty X.
Empty fibres are finite; no surjectivity is inferred or assumed. The zero ring
is allowed in affine opens and yields an empty spectrum. Nonreduced schemes
and arbitrary characteristics are included. There is no n or index-set
parameter. Infinite disjoint unions of points can be locally quasi-finite
without quasi-compactness and may have infinite fibres. The localization
ℤ → ℚ is Mathlib-quasi-finite but not finite type; this demonstrates why its
bare predicate is insufficient. The universe u is explicitly bound and
arbitrary, matching Mathlib's scheme category; there is no independently
smaller test universe or unbound variable.

Mismatch repaired: the worker report's infinite algebraic field-extension
example was misleading as a separator from Mathlib's predicates. Such an
extension also violates Mathlib's finite residue-field requirement. I replaced
that explanation by ℤ → ℚ and retained the infinite-extension example only
with its correct two failures. No mathematical mismatch in the Lean or node
was found, so neither was rewritten. No new definition node, dependency module,
or statement correction is needed. All four definitions are genuine formulas,
with no sorry, proof, or hidden data; the empty node proof needs no proof-step
docstring. Source tags and blueprint id occur in every declaration docstring,
and the sole import supplies the used notions. The recorded primary signature
is verbatim equal to the file's signature up to `:=`.

Validation: `scompile.py C1 pqf-def-quasifinite` on the delivered module
compiled on the server in 1.7 seconds with exit code 0 and no warnings.


## Reviewer fix (R-pdq1107, stage 2)

The delivered clause 1 used Mathlib `RingHom.FiniteType` with `RingHom.QuasiFiniteAt`, a second
form of the ring-level notion of Stacks Tag 00PL which the project records as
`Algebra.IsQuasiFiniteAtPrime` (def-weil-pbc-ring-map-quasi-finite-at-prime, H4/H12). The two are
equivalent under finite type (`Algebra.quasiFiniteAt_iff_isOpen_singleton_fiber`), but every citer
must use one form. `IsQuasiFiniteAtPoint` now reads
`letI := (f.appLE V U e).hom.toAlgebra; ∃ hft : Algebra.FiniteType Γ(S, V) Γ(X, U),
Algebra.IsQuasiFiniteAtPrime Γ(S, V) Γ(X, U) (hU.primeIdealOf ⟨x, hx⟩)`, exactly the form of the
landed lem-weil-pbc-isolated-fibre-point-quasi-finite-affine-pairs. The imports are now
`Mathlib.AlgebraicGeometry.Fiber`, `Mathlib.AlgebraicGeometry.Morphisms.FiniteType` and
`Sheaf.RingTheory.QuasiFiniteAtPrime`. Clauses 2, 3 and finite fibres are unchanged.
