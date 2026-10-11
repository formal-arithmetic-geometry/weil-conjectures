## Worker report

The module `Sheaf.RingTheory.IsN1OfFiniteDomainExtension` states
`isN1_of_finite_domain_extension`, with its proof left as `sorry` as required in stage 2.
No definitions are introduced, and the node is changed only in its `lean` field.

Hypotheses and clauses, matched individually:
- Integral domains A and B: `(A : Type uA) (B : Type uB)` with `[CommRing A] [IsDomain A]`
  and `[CommRing B] [IsDomain B]`.
- Inclusion A ⊆ B: `[Algebra A B]` and
  `(hAB : Function.Injective (algebraMap A B))`. This describes an arbitrary embedding,
  so its image identifies A with the specified subring of B; it does not require a literal
  subtype carrier or a proper inclusion.
- A Noetherian: `[IsNoetherianRing A]`, exactly all ideals finitely generated.
- B finite as an A-module: `[Module.Finite A B]`, using the same algebra map.
- The fraction field of B: `(L : Type uL) [Field L] [Algebra B L] [IsFractionRing B L]`.
- Its integral closure finite over B, equivalently B N-1: `(hB : IsN1 B L)`;
  the recorded definition unfolds to `Module.Finite B (integralClosure B L)`.
- The fraction field of A: `(K : Type uK) [Field K] [Algebra A K] [IsFractionRing A K]`.
- The integral closure of A finite over A, equivalently A N-1: conclusion `IsN1 A K`,
  unfolding to `Module.Finite A (integralClosure A K)`.
The four carrier universes are explicit and independent; no test-object quantification is
restricted to a smaller universe. No field-extension degree, separability, normality, or
extra scalar tower is assumed.

Dependency declarations read and used:
- `Mathlib.RingTheory.Noetherian.Defs`: `IsNoetherianRing`, its docstring and
  `isNoetherianRing_iff_ideal_fg`, matching the Noetherian dependency.
- `Mathlib.RingTheory.Finiteness.Defs`: `Module.Finite`, its full class declaration and
  docstring. Available through the Japanese-domain import; no redundant direct import.
- `Sheaf.RingTheory.JapaneseDomain`: `IsN1`, full definition and docstring read; the
  dependency also records `IsN2` and `isN1_of_isN2`, but this item needs only N-1.
- `Mathlib.RingTheory.IntegralClosure.Algebra.Basic`: `integralClosure`, full definition
  and docstring read, reused through `IsN1` rather than copied.

Source verification: the local literature checkout is absent. Opened the authoritative
Stacks page https://stacks.math.columbia.edu/tag/032K (Lemma 10.161.7), which states the
N-1 descent for a Noetherian domain and a finite inclusion of domains. The source's hint
is expanded in the node's four proof steps, all included with dependency ids in the
Lean declaration docstring. No statement correction is needed.

Edge cases checked mathematically before writing:
- A = B and the identity embedding are allowed: descent becomes the same N-1 property,
  independent of the chosen models of the fraction fields.
- Fields and finite field extensions are allowed, with no restriction on characteristic;
  a field is already its own normalization.
- The zero ring is excluded precisely by the source's domain hypothesis (`IsDomain`).
- Noninjective finite algebra maps are excluded precisely by the source's inclusion;
  `[Algebra A B]` alone would not have expressed it.
- A need not be normal; replacing N-1 by integrally closed would change the statement.
- No finite generation of a field extension is added; the theorem assumes only the finite
  module extension B/A already stated in the node.

Searches for an existing statement (all through the prescribed tools or read-only rg):
- `msearch.py leansearch`: "The integral closure of a Noetherian domain in its fraction
  field is finite if a finite domain extension has finite normalization". Service returned
  Internal Server Error; recorded as unavailable, not as a no-match verdict.
- `msearch.py leanfinder`: "N-1 descends along a finite injective extension of Noetherian
  integral domains". Eight hits, including `fg_of_fg_of_fg`,
  `IsIntegralClosure.isNoetherian`, and finite-type Noetherian results; none states N-1
  descent along a finite inclusion.
- `msearch.py loogle`: "integralClosure, Module.Finite". Successful, zero hits.
- `msearch.py grep` in Mathlib/RingTheory:
  `IsN1|[Nn]ormalization.*finite|[Ff]inite.*integralClosure|[Jj]apanese`.
  Seven hits, concerning fraction fields of integral closures, different ideals,
  valuations, and Zariski's main theorem; no matching descent theorem.
- Read-only `rg -n 'IsN1|n1_descends|N-1|finite.*integralClosure'` over upstream
  `WeilConjectures` and this project's `lean/Sheaf`. Upstream hits concern normalization
  of finite-type algebras over fields; project hits are the N-1 definition, localization,
  analytically unramified domains and finite-type Z-domains. None is this statement.
- `grep -rn 'lem-weil-pbc-n1-descends-finite-domain-extension'` over upstream
  `WeilConjectures`: no hits.
- Name-collision `rg` for `isN1_of_finite|IsN1OfFinite` over Mathlib, upstream,
  project Lean, and `dag/lean_names_upstream.json`: no hits.

No disputed statement or dependency fault was found. The only unfinished proof is the
named theorem `isN1_of_finite_domain_extension`; its complete natural-language proof and
source are in its docstring and existing DAG node.

## Second reading by G1

I read the node statement, its Stacks source (Algebra, Lemma 10.161.7, Tag 032K),
its dependency records, and `Sheaf/RingTheory/IsN1OfFiniteDomainExtension.lean` item by
item. The objects and hypotheses render as follows:

- Integral domains `A : Type uA` and `B : Type uB` are rendered by
  `[CommRing A] [IsDomain A] [CommRing B] [IsDomain B]`.
- The inclusion `A ⊆ B` is rendered by `[Algebra A B]` together with
  `hAB : Function.Injective (algebraMap A B)`; this is the appropriate abstract
  inclusion and imposes no extra properness assumption.
- Noetherianity of `A` is `[IsNoetherianRing A]`, and finiteness of `B` over `A` is
  `[Module.Finite A B]`, with the given algebra structure.
- Fraction fields are explicitly introduced as `K` and `L` with
  `[Field K] [Algebra A K] [IsFractionRing A K]` and
  `[Field L] [Algebra B L] [IsFractionRing B L]`.
- The premise that the integral closure of `B` in `L` is finite is exactly
  `hB : IsN1 B L`, and the conclusion is exactly `IsN1 A K`.

The theorem's conclusion has the same single clause and quantifier order as the node;
there are no extra separability, normality, finite-degree, or scalar-tower hypotheses.
The theorem body is intentionally `sorry` and the declaration docstring records all
four proof steps and their dependency nodes. No mismatch was found and no Lean change
was required.

Edge cases checked: the identity extension `A = B` is admitted; field examples and all
characteristics are admitted; the zero ring is excluded by `IsDomain`; no restriction on
`n` or an index set occurs; and all four carrier universes remain independent. The
fraction-field hypotheses prevent degenerate carrier choices.

I repeated the existing-definition searches (LeanSearch, LeanFinder/Loogle, and `rg` in
Mathlib, upstream `WeilConjectures`, and project `lean/Sheaf`). They found no theorem
expressing this N-1 descent, and the declaration name does not collide with existing
names. The recorded `IsN1` dependency is the project's Japanese-domain definition, not a
private copy. Compilation with `scompile.py` succeeds with only the permitted `sorry`.
