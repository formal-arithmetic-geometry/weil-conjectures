## Worker report

The module `Sheaf.AlgebraicGeometry.QuasiCompactFlatMonomorphismRingedImage` states
`AlgebraicGeometry.quasiCompact_flat_monomorphism_ringed_image`, with one `sorry` and
no new definitions. The node's natural-language statement is unchanged.

Hypothesis and clause correspondence:

- Schemes and the arrow: `{X S : Scheme.{u}} (f : X ⟶ S)`. The universe `u` is
  explicitly bound; `set_option autoImplicit false` forbids accidental implicit variables.
- Quasi-compact, flat, monomorphism: `[QuasiCompact f] [Flat f] [Mono f]`.
  Mathlib's `Mono` is precisely cancellation of postcomposition on all test morphisms;
  its flatness is equivalent to flatness of the actual structural stalk maps.
- The image E is `Set.range f`. Every occurrence uses that actual image.
- Subspace topology and inverse-image sheaf: exactly the dependency's
  `LocallyRingedSpace.ringedSubspace S.toLocallyRingedSpace (Set.range f)`.
  No substitute sheaf or scheme-theoretic image occurs in the conclusion.
- Locally ringed identification: the first conjunct supplies locality of the actual
  subspace stalks (`hlocal`), then an isomorphism of locally ringed spaces
  `X.toLocallyRingedSpace ≅ LocallyRingedSpace.locallyRingedSubspace ... hlocal`.
  The equality `e.hom.toShHom ≫ LocallyRingedSpace.ringedSubspaceι ... =
  f.toLRSHom.toShHom` makes this the identification induced by f over S.
  Only proof data are supplied to the existing locally ringed bundling. The inverse
  isomorphism makes the canonical inclusion local as well, since it is f composed with
  the inverse of e. Thus the over-S equation is also an equation of locally ringed maps.
- Generalization stability: `StableUnderGeneralization (Set.range f)`, whose definition
  sends membership of s and `t ⤳ s` to membership of t. This is the stated direction.
- Retrocompactness: `IsRetrocompact (Set.range f)`, defined as compactness of E ∩ U
  for each compact open U, with no assumption that S itself is quasi-compact.
- All test schemes and morphisms: `∀ (T : Scheme.{u}) (g : T ⟶ S)`.
  The biconditional is `(∃! a : T ⟶ X, a ≫ f = g) ↔ Set.range g ⊆ Set.range f`.
  Its equality uses the category's order of composition, so means f after a equals g.
- Uniqueness over the base: for every scheme Y and arrow g with the same three
  hypotheses, `Set.range g = Set.range f → ∃! e : X ≅ Y, e.hom ≫ g = f`.
  The uniqueness is of the isomorphism itself, including its morphism over S.
- There is no finite presentation, Noetherianity, or separation binder.

Statement dependencies read and used:

- `def-pc-scheme`: `AlgebraicGeometry.Scheme`, `Scheme.Hom`, in
  `Mathlib.AlgebraicGeometry.Scheme` (via the public morphism imports).
- `def-weil-flat-morphism`: `AlgebraicGeometry.Flat`, in
  `Mathlib.AlgebraicGeometry.Morphisms.Flat`; read its class and stalk criterion.
- `def-weil-pbc-scheme-conventions`: a convention-only node with no declaration.
  Quasi-compactness is Mathlib's `AlgebraicGeometry.QuasiCompact` in
  `Mathlib.AlgebraicGeometry.Morphisms.QuasiCompact`.
- `def-a1-ringed-subspace`: `AlgebraicGeometry.LocallyRingedSpace.ringedSubspace`,
  `ringedSubspaceι`, and `locallyRingedSubspace`, in
  `Sheaf.AlgebraicGeometry.RingedSubspace`. Their full definitions were read; the
  structure sheaf is `TopCat.Sheaf.pullback` and the inclusion uses its adjunction unit.

The module privately imports the recorded proof-dependency modules that are stated:
`Sheaf.AlgebraicGeometry.FlatMonomorphismLocalStructure`,
`Mathlib.AlgebraicGeometry.Morphisms.FiniteType`,
`Mathlib.AlgebraicGeometry.Morphisms.ClosedImmersion`,
`Mathlib.AlgebraicGeometry.IdealSheaf.Subscheme`,
`WeilConjectures.Mathlib.AlgebraicGeometry.Morphisms.SchemeTheoreticallyDominant`,
`WeilConjectures.AlgebraicGeometry.InverseImageStructureStalkIso`, and
`Sheaf.AlgebraicGeometry.StalkIsomorphismLifting`. The Mathlib leaf proof inputs
`Flat.generalizingMap` and `TopCat.Presheaf.isIso_iff_stalkFunctor_map_iso` are
provided by the additional private imports `Morphisms.UniversallyOpen` and
`Topology.Sheaves.Stalks`. The topological inverse image and locally ringed morphism
proof inputs are already public dependencies of RingedSubspace.

Source checked: the primary Numdam scan
https://www.numdam.org/article/SAC_1967-1968__2__A5_0.pdf,
printed pp. 1–2, §1 Propositions 1.1 and 1.2(i), Corollary 1.3.
Proposition 1.2(i) expressly identifies X with the induced ringed subspace. The
factorization assertion follows from that identification and the inverse-image sheaf
mapping property; the node's seven-step proof is retained in the theorem docstring.

Edge cases checked before drafting: empty X gives the empty inverse-image subspace,
vacuous locality, and a lift exactly for empty T; empty S permits only empty sources.
For f the identity the image is all S and the lift is g. For a localization such as
Spec Q to Spec Z the image need not be open, so the conclusion uses the arbitrary
ringed subspace, never an open subscheme. For U empty, the retrocompact intersection
is empty. Surjective quasi-compact flat monomorphisms reduce to isomorphisms. No
nonempty, affine, finite presentation, reducedness, or Noetherianity restriction appears.
The test scheme universe is the same as S, consistent with Mathlib's scheme category;
it is not an independent smaller universe making the tests vacuous.

Searches actually performed (2026-10-24):

- msearch LeanFinder: "A quasi compact flat monomorphism identifies its source with
  its ringed image and factors uniquely morphisms whose image lies in that image".
  Eight hits, including `Flat.isIso_of_surjective_of_mono` (requires surjectivity) and
  `IsOpenImmersion.of_flat_of_mono` (requires local finite presentation). Neither is
  the full statement. Both full signatures were read in FlatMono.lean.
- msearch Loogle: `"Flat", "QuasiCompact", "IsEmbedding"`: zero hits.
- msearch grep: `flat.*mono|mono.*flat|pro.?open`, Mathlib AlgebraicGeometry:
  15 hits, chiefly FlatMono and descent; no full ringed-image statement.
- msearch LeanSearch: "A quasi compact flat monomorphism is a topological embedding
  with isomorphic stalk maps and represents morphisms whose image is contained in
  its image": eight hits, including the same two restricted results, QuasiCompact,
  Flat.of_stalkMap, and preimmersion facts; no exact match.
- Direct rg over `lean/WeilConjectures` and `lean/Sheaf` for flat/mono combinations,
  retrocompact, and ringedSubspace found the existing RingedSubspace construction,
  local-structure and stalk-lifting inputs, and related affine-embedding results.
  No full statement was found. Searching those trees and `dag/lean_names_upstream.json`
  for the proposed declaration name returned no collision. Searching the upstream
  tree for the item id returned no existing declaration.

No statement fault, correction, new node, or dependency repair was needed.

## Second reading by Q69

Maintainer second reading of delivery 83bfeabe038d (2026-10-24). This replaces the author's
self-check delivered in this section. It changes no Lean, no node record and no mathematics.

The node statement, clause by clause, with the Lean that renders it:

1. f : X → S, a morphism of schemes. Lean: `{X S : Scheme.{u}} (f : X ⟶ S)`. Correct.
2. Hypotheses: quasi-compact, flat, monomorphism (postcomposition is injective on Hom(T,X)).
   Lean: `[QuasiCompact f] [Flat f] [Mono f]`. These are the Mathlib notions recorded by
   def-weil-pbc-scheme-conventions and def-weil-flat-morphism, and `Mono` is cancellation
   for all test schemes. Nothing more is assumed: no lfp, Noetherian or separation hypothesis,
   and no extra universe. Correct.
3. E = f(|X|) as a ringed subspace S|_E = (E, i⁻¹O_S). Lean: `Set.range f` and
   `LocallyRingedSpace.ringedSubspace S.toLocallyRingedSpace (Set.range f)`. I read
   Sheaf/AlgebraicGeometry/RingedSubspace.lean: the carrier is `TopCat.of S` (subspace
   topology), the sheaf is `TopCat.Sheaf.pullback` along the inclusion, and `ringedSubspaceι`
   is the adjunction unit. This is exactly def-a1-ringed-subspace. Correct.
4. "f canonically identifies X with S|_E as a locally ringed space." Lean: ∃ locality proof
   `hlocal` (Prop data only, as the dependency prescribes) and ∃ an iso of locally ringed
   spaces `e`, with `e.hom.toShHom ≫ ringedSubspaceι = f.toLRSHom.toShHom`. The equation pins
   e: a ringed map into (E, i⁻¹O_S) over the inclusion is determined by its composite with ι
   (the base map because ι is injective; the sheaf map because of the pullback–pushforward
   adjunction). So this is the canonical identification, not an arbitrary iso. Correct.
5. E is stable under generalization: s ∈ E and s ∈ closure{t} give t ∈ E. Lean:
   `StableUnderGeneralization (Set.range f)`, i.e. Mathlib Inseparable.lean:250
   `∀ ⦃x y⦄, y ⤳ x → x ∈ s → y ∈ s`. Here y ⤳ x means x ∈ closure{y}, which is the node's
   direction. Correct.
6. E is retrocompact. Lean: `IsRetrocompact (Set.range f)`, i.e. Constructible.lean:52
   `∀ U, IsCompact U → IsOpen U → IsCompact (s ∩ U)`. This is the node's definition and does
   not assume S quasi-compact. Correct.
7. For all T and g : T → S, there is a unique a with f ∘ a = g iff g(|T|) ⊆ E. Lean:
   `∀ T g, (∃! a, a ≫ f = g) ↔ Set.range g ⊆ Set.range f`. Both directions are there, and
   uniqueness is inside the left side. Correct.
8. Two qc flat monos with the same image are uniquely isomorphic over S. Lean:
   `∀ Y g [QuasiCompact g] [Flat g] [Mono g], range g = range f → ∃! e : X ≅ Y, e.hom ≫ g = f`.
   Both maps carry the hypotheses, and the uniqueness is of the iso over S. Correct.

Edge cases. Empty X: E = ∅, `hlocal` is vacuous, the iso is with the empty space, and only
an empty T lifts. Identity f: E = S. Spec ℚ → Spec ℤ: E is not open, so the arbitrary-subset
ringed subspace is needed; the statement uses it, not an open subscheme. Empty U in the
retrocompactness clause is trivial. Test schemes lie in the same universe u as S, which is
Mathlib's scheme category; this is not a restriction.

Records and gates. `lean.statement` is verbatim the signature in the file (checked by diff).
stmt_deps are the four statement notions, and each Lean name comes from those records or from
Mathlib (Mono, StableUnderGeneralization, IsRetrocompact are spelled out in the node text).
No theorem-module definition is used in the statement. There are no new definitions, the proof
is only `sorry`, and the docstrings carry the source place, `(blueprint: …)` and the 7-step
proof. The private proof imports exist on side-live and import no downstream module. Duplicate
search: Mathlib FlatMono.lean has only `Flat.isIso_of_surjective_of_mono` (surjective case)
and `IsOpenImmersion.of_flat_of_mono` (lfp case), so the theorem is not existing.

Mismatches found: none in the Lean or the records. The only change is this section.
