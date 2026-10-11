## Worker report

The module `Sheaf.AlgebraicGeometry.ProperFibreIdempotentImage` states
`AlgebraicGeometry.Scheme.Hom.exists_section_restricting_to_fiber_idempotent`.
Its only proof is `sorry`; it defines no new notion and changes no node statement.

Hypothesis and clause correspondence:

- Schemes X and S: `{X S : Scheme.{u}}`, with the universe explicitly bound.
- Morphism f: `(f : X ⟶ S)`.
- Properness [def-weil-proper-morphism]: `[IsProper f]`.
- Base point: `(s : S)`.
- Scheme-theoretic fibre [def-pc-scheme-fibre]: `f.fiber s`, with projection `f.fiberι s`.
- Element of H^0(X_s,O): `(e : Γ(f.fiber s, ⊤))`. Degree-zero structure-sheaf
  cohomology is precisely global sections, not higher module cohomology.
- Idempotence: `(he : IsIdempotentElem e)`, namely `e * e = e`.
- Membership in the image of the canonical map from the pushforward stalk:
  `∃ U, s ∈ U ∧ ∃ h t, (f.fiberι s).appLE (f ⁻¹ᵁ U) ⊤ h t = e`.
  Here `t : Γ(X, f ⁻¹ᵁ U)` represents an element of `(f_*O_X)_s`. Conversely
  every stalk element has such a representative, as Mathlib's
  `TopCat.Presheaf.exists_germ_eq` states (Topology/Sheaves/Stalks.lean:433).
  The canonical map to fibre sections sends this germ to the pullback of its
  representative along `f.fiberι s`, exactly the displayed `appLE` map.
  The proof binder `h : ⊤ ≤ (f.fiberι s) ⁻¹ᵁ (f ⁻¹ᵁ U)` lets `appLE` target
  global sections. It imposes no additional geometric condition: the range of
  `fiberι` is `f ⁻¹' {s}` (`Scheme.Hom.range_fiberι`), so `s ∈ U` implies it.
  Proof irrelevance makes the map independent of the choice of `h`.
  No idempotence condition is put on `t`, since the node only asks for image
  membership, not an idempotent lift. No stalk element is discarded: taking
  its representative and taking a representative's germ give both directions.

Dependency declarations read and used:

- `Mathlib.AlgebraicGeometry.Morphisms.Proper`, `AlgebraicGeometry.IsProper`:
  separated, universally closed, locally of finite type; universal closedness
  implies quasi-compactness, giving the node's finite-type condition.
- `Mathlib.AlgebraicGeometry.Fiber`, `AlgebraicGeometry.Scheme.Hom.fiber` and
  `fiberι`: the chosen pullback along `S.fromSpecResidueField s` and first projection.
- Mathlib `Scheme.Hom.appLE` (AlgebraicGeometry/Scheme.lean:196) is the actual
  induced ring map on sections, followed by restriction; no arbitrary map is used.

Source checked: [Stacks Tag 0G7X](https://stacks.math.columbia.edu/tag/0G7X),
currently Lemma 36.32.7. The local literature file is absent on this machine,
so the official tag statement and complete proof were read online. The node's
old numbering says Derived Categories Lemma 21.16.1; its stable tag is correct.
The docstring follows all nine DAG proof steps, including the general
Noetherian approximation argument; local Noetherianity is not a hypothesis.

Edge cases checked: empty X and empty fibre give the zero ring, whose unique
idempotent is the restriction of the zero section (U may be top). Empty S
has no s, so no instance of the quantified premise. Both e=0 and e=1 are
included. Disconnected or nonreduced fibres, non-Noetherian bases, and all
characteristics remain included. The source proof's opening description
using two nonempty clopen pieces is unnecessary for trivial idempotents and
is not an extra hypothesis here. Schemes and their fibres use the same
Mathlib universe u without bounds excluding cases.

Searches for an existing statement:

- msearch.py leanfinder: “For a proper morphism of schemes every idempotent
  section on a fibre lies in the image of the stalk of the pushforward
  structure sheaf”. Eight hits: spreading out, quasi-separated sections,
  stalk range, and affine-transition limits; no proper-fibre idempotent lemma.
- msearch.py loogle: `AlgebraicGeometry.Scheme.Hom.fiberι`. Ten hits giving
  projection, range, factorization and fibre-homeomorphism declarations;
  none states the desired image result.
- msearch.py grep `proper.*idempotent|idempotent.*fiber|stalk.*fiber` in
  Mathlib/AlgebraicGeometry: nine hits on projective-spectrum stalk-to-fibre
  maps, not the proper-fibre statement.
- rg `fibre.*(stalk|section)|stalk.*(fibre|fiber)|idempotent.*(fibre|fiber)`
  in the source WeilConjectures and project lean/Sheaf: related finite-flat
  and etale material, no match. grep of the exact node id in the source: no hit.
- Exact new declaration name searched in dag/lean_names_upstream.json,
  project Lean, source Lean and Mathlib: no hit.

Server compilation via scompile.py passed cleanly in 1.7 seconds. No
STATEMENT-DISPUTED issue, new node, dependency replacement, or correction.

## Second reading by Q1

Node objects and hypotheses, matched in order:

- `X S : Scheme.{u}` are the two schemes of the node; the shared universe is the
  universe used by Mathlib's scheme category and does not add a finiteness restriction.
- `f : X ⟶ S` is the morphism, with `[IsProper f]` exactly the node's properness
  hypothesis (Mathlib's class extends separated, universally closed, and locally finite type).
- `s : S` is the chosen base point.
- `e : Γ(f.fiber s, ⊤)` is a global section of the structure sheaf on the
  scheme-theoretic fibre `f.fiber s`, using the dependency declaration exactly.
- `he : IsIdempotentElem e` is the equation `e * e = e`, with no condition added
  to a lift on `X`.

The conclusion is rendered as
`∃ U : S.Opens, s ∈ U ∧ ∃ h : ⊤ ≤ (f.fiberι s) ⁻¹ᵁ (f ⁻¹ᵁ U),
∃ t : Γ(X, f ⁻¹ᵁ U), (f.fiberι s).appLE (f ⁻¹ᵁ U) ⊤ h t = e`.
Here `U` and `t` are precisely a representative neighbourhood and section for an
 element of the pushforward stalk, and `appLE` is the canonical restriction along
the fibre projection. The auxiliary inclusion proof `h` is required by `appLE` and
is propositionally irrelevant; it adds no geometric hypothesis. Thus this is
exactly image membership in the map named by the node. Quantifier order and all
clauses agree, with no extra conclusion or omitted condition.

Edge cases were checked: `e = 0` and `e = 1`, disconnected or nonreduced fibres,
empty schemes/fibres, empty `S` (vacuous point quantifier), arbitrary
characteristic, and non-Noetherian bases are all covered. No nonemptiness,
Noetherian, finite type, or characteristic assumption appears in the Lean.
The shared scheme universe is forced by the category of schemes and does not
exclude any instance represented by the node.

I repeated the existing-definition searches with LeanFinder/Loogle and grep over
Mathlib, `WeilConjectures`, and `lean/Sheaf`; only generic fibre, stalk, and
idempotent declarations were found. The exact declaration name and node id have
no existing match. The two recorded dependencies resolve to Mathlib's
`AlgebraicGeometry.IsProper` and `Scheme.Hom.fiber`/`fiberι`; no private copy or
dependency module is needed.

No mismatch was found, so no statement or source module change was required.
