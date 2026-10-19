## Worker report

The module `Sheaf.AlgebraicGeometry.ClosedProperSupportLocality` states
`AlgebraicGeometry.Scheme.closed_proper_support_locality`, with one `sorry` proof.
It states both numbered clauses as a conjunction. No definitions or dependency nodes
are added, and no mathematical statement is corrected.

Hypotheses and clauses, in order:

- Schemes and the morphism `p : T → S` are `{T S : Scheme.{u}} (p : T ⟶ S)`.
- Local finite type is `[LocallyOfFiniteType p]`; closedness of `C` is the bundled
  parameter `(C : TopologicalSpace.Closeds T)`.
- Properness means the recorded `Scheme.IsClosedSubsetProperOver`, which applies
  `IsProper` to the composite of the vanishing-ideal subscheme immersion with `p`.
  Thus it uses the reduced induced closed structure, not a new support predicate.
- Clause (1) universally quantifies `(S' : Scheme.{u}) (w : S' ⟶ S)` without any
  property of `w`. The ambient base change is `pullback p w`, its map to the base
  is `pullback.snd p w`, and its map to `T` is `pullback.fst p w`.
  `C.preimage (pullback.fst p w).continuous` is exactly the closed inverse image.
  The implication from `IsClosedSubsetProperOver p C` gives its properness over `S'`.
- Clause (2) quantifies `(I : Type v) (Sᵢ : I → Scheme.{u})
  (w : ∀ i, Sᵢ i ⟶ S)` with `[∀ i, Etale (w i)]`.
  `(∀ s : S, ∃ (i : I) (x : Sᵢ i), w i x = s)` is joint surjectivity.
  The next hypothesis says every closed inverse image under `pullback.fst p (w i)`
  is proper over `Sᵢ i` via `pullback.snd p (w i)`. The conclusion is precisely
  `IsClosedSubsetProperOver p C`.
- No quasi-compactness assumption occurs on `p`, `S`, or the family members.

Dependency declarations read and used:

- `Mathlib.AlgebraicGeometry.Scheme`: `AlgebraicGeometry.Scheme` and `Scheme.Hom`.
- `Mathlib.AlgebraicGeometry.Morphisms.FiniteType`:
  `AlgebraicGeometry.LocallyOfFiniteType` (the local-finite-type component of the node).
- `Sheaf.AlgebraicGeometry.ClosedSubsetProperOverBase`:
  `AlgebraicGeometry.Scheme.IsClosedSubsetProperOver`.
- `Mathlib.CategoryTheory.Limits.Shapes.Pullback.HasPullback`:
  `CategoryTheory.Limits.pullback`, `pullback.fst`, and `pullback.snd`;
  imported through `Mathlib.AlgebraicGeometry.Pullbacks`, supplying scheme pullbacks.
- `Mathlib.AlgebraicGeometry.Morphisms.Etale`: `AlgebraicGeometry.Etale`.
- `Mathlib.Topology.Sets.Closeds`: `TopologicalSpace.Closeds.preimage`.

The recorded modules for stated proof dependencies are imported without `public`:
`ReducedInducedClosedSubscheme`, `ClosedSubsetProperOverBaseProperties`, and
`FpqcFinerThanEtale`; Mathlib's closed-immersion, properness, pullback, finite-type,
and small-étale-site modules supply the Mathlib proof leaves. The proof dependency
`lem-weil-pbc-proper-morphism-fpqc-descent` has no recorded Lean module and hence no
import yet. The declaration docstring gives all four proof steps and their node IDs.

Sources checked: the local Stacks source `coherent.tex`,
`lemma-base-change-closed-proper-over-base` (0CYP), and `descent.tex`,
`lemma-descending-property-proper-over-base` (0F4J). Both assume exactly local finite
type for the ambient morphism. The latter applies to fpqc covers; the existing
étale-to-fpqc statement provides the specialization to arbitrary étale families.

Edge cases: `C = ∅`, empty `T`, and empty `S` are all allowed. An empty family is
allowed: joint surjectivity then forces `S` to be empty. No `Nonempty I`, finite
index restriction, or quasi-compactness restriction is imposed. The index universe
`v` is arbitrary and independent of the scheme universe. Arbitrary non-flat base
change is allowed, and the statement does not incorrectly identify a pullback of
a reduced scheme with a reduced scheme.

Searches performed before writing:

- `msearch.py` LeanFinder: “Closed subsets proper over the base are stable under
  base change and descend under jointly surjective etale families”. Eight results
  concern ordinary proper/universally closed morphisms and generic descent, including
  `IsProper.instIsZariskiLocalAtTarget` and
  `descendsAlong_universallyClosed_surjective_inf_flat_inf_quasicompact`; no exact match.
- `msearch.py` Loogle: `AlgebraicGeometry.IsProper, AlgebraicGeometry.Etale`;
  successful search, zero hits.
- `msearch.py` grep: `IsClosedSubsetProperOver|closed_subset_proper` in
  `AlgebraicGeometry`; successful search, zero Mathlib hits.
- `msearch.py` LeanSearch: “A closed subset proper over the base remains proper
  after arbitrary base change and properness descends along an etale covering”;
  service unavailable (Internal Server Error), recorded as unavailable.
- `rg` of `WeilConjectures` and `lean/Sheaf` for proper support, closed properness,
  and `IsClosedSubsetProperOver`: the existing predicate and structure-independence
  theorem were found and read; other hits concern modules, coherent supports,
  approximation, or special base changes, not this two-clause statement.
- Search for the item ID in upstream `WeilConjectures`: no hits. Search for the
  proposed declaration name `closed_proper_support_locality` in upstream,
  `lean/Sheaf`, and `dag/lean_names_upstream.json`: no hits.

No statement dispute or node fault was found. Compilation and delivery validation
are performed with the mandated server-only tools.

## Second reading by NQ

I independently read the node, its sandbox signature, all five statement-dependency
records and their actual declarations, the reduced-induced-structure and
structure-independence modules, and Stacks coherent.tex, lemma-base-change-closed-
proper-over-base (0CYP), and descent.tex, lemma-descending-property-proper-over-base
(0F4J). Both source statements assume only local finite type for the ambient
morphism; the latter uses an fpqc covering. The recorded étale-to-fpqc theorem
supplies precisely the specialization here, without quasi-compact covering members.

Object, hypothesis, and conclusion inventory and verdicts:

1. Arbitrary schemes T and S and a scheme morphism p: `{T S : Scheme.{u}}`
   and `(p : T ⟶ S)`. Read `Scheme` and `Scheme.Hom` in Mathlib; these are locally
   ringed spaces locally isomorphic to affine spectra and their morphisms. Exact.
2. Local finite type: `[LocallyOfFiniteType p]`. Its affine-section finite-type
   condition is the recorded notion, not finite type with quasi-compactness. Exact.
3. Closed subset C: `(C : TopologicalSpace.Closeds T)`. The bundle includes precisely
   closedness and no subscheme structure or reducedness assumption. Exact.
4. Properness of C: `IsClosedSubsetProperOver p C`. Opened the definition: it is
   `IsProper ((IdealSheafData.vanishingIdeal C).subschemeι ≫ p)`. Opened
   `reduced_induced_closed_subscheme`: this immersion has image C, reduced source,
   the vanishing ideal, and uniqueness over T. Mathlib `IsProper` is separated,
   universally closed, locally of finite type. This is the node's properness. Exact.
5. Clause (1), arbitrary base map: `∀ (S' : Scheme.{u}) (w : S' ⟶ S)` with no
   flatness, étaleness, surjectivity, or finiteness requirement. Exact.
6. Clause (1), fibre product and inverse image: `pullback p w`, `pullback.fst p w`
   to T, and `pullback.snd p w` to S'. Read the categorical pullback and projections;
   scheme pullbacks are supplied by Mathlib. Read `Closeds.preimage`, whose carrier
   is the set-theoretic inverse image. Exact.
7. Clause (1), implication: `IsClosedSubsetProperOver p C →
   IsClosedSubsetProperOver (pullback.snd p w)
   (C.preimage (pullback.fst p w).continuous)`. This is exactly preservation under
   arbitrary base change. Local finite type of the projection is inferred from p.
8. Clause (2), family: `∀ (I : Type v) (Sᵢ : I → Scheme.{u})
   (w : ∀ i, Sᵢ i ⟶ S) [∀ i, Etale (w i)]`. Read Mathlib `Etale`, affine-locally
   étale ring maps, the dependency's recorded definition. No stronger condition.
9. Clause (2), joint surjectivity: `∀ s : S, ∃ (i : I) (x : Sᵢ i), w i x = s`.
   This allows each point to lift through any member, without requiring individual
   members to be surjective. Exact quantifier order.
10. Clause (2), all pulled-back supports proper: `∀ i,
    IsClosedSubsetProperOver (pullback.snd p (w i))
    (C.preimage (pullback.fst p (w i)).continuous)`. The objects and maps are the
    same fibre products as in (1), now for each family member. Exact.
11. Clause (2), conclusion: `IsClosedSubsetProperOver p C`, following the two
    preceding hypotheses. The outer conjunction states both numbered clauses.
    No quasi-compactness assumption on p, S, or any Sᵢ is present. Exact.

Edge cases: bottom/empty C, empty T and empty S are admitted. An empty I is admitted;
its surjectivity hypothesis forces S empty, as it should. Universes u and v are
explicitly bound, with independent arbitrary index universe v; schemes share the
ambient scheme universe, which may be enlarged to contain any given family.
There is no test-object universe making a hypothesis vacuous. No field, characteristic,
Noetherian, nonempty, or cardinality restriction occurs. Zero objects and n = 0 are
not additional parameters of this scheme statement. Nonreduced base changes are
allowed: the conclusion uses the reduced structure on the inverse-image subset,
not a claim that a base-changed reduced scheme remains reduced.

Independent searches (2026-10-15): LeanFinder query “Properness of the reduced
induced subscheme of a closed set is preserved by change of base and can be checked
on surjective etale covers” returned eight ordinary proper-morphism results,
including `IsProper.instIsZariskiLocalAtTarget` and `IsProper.of_comp`; none states
this closed-subset theorem. Loogle for `IsProper.isStableUnderBaseChange` returned
that generic stability instance; I read Proper.lean and it concerns morphisms,
not reduced supports or this descent statement. LeanSearch for “A closed subset
proper over a scheme remains proper under arbitrary base change and properness
descends along jointly surjective etale maps” was unavailable (Internal Server Error).
Independent rg searches used `closed_proper`, `ClosedSubsetProper`, and both orders
of “proper” and “support” across Mathlib algebraic geometry, upstream WeilConjectures,
and project Lean. The narrower `IsClosedSubsetProperOver` and proposed declaration
name search, also in the upstream name inventory, found no duplicate. I opened
`isClosedSubsetProperOver_union_preimage`: its preimage clause assumes a proper
map over a fixed base, a different statement. The existing structure-independence
and module-support results also do not state this theorem.

No new definition nodes or dependency modules are delivered, and no statement_change
is present or needed. All required dependency notions already exist and are used
without private copies. The docstring retains each of the node's four proof steps,
including the tensor-quotient calculation and the every-closed-structure direction.
The module has exactly one theorem, with whole proof `sorry`, no definitions,
no hidden variables, and no file-local instances or notation. Its recorded signature
matches the file verbatim. No mathematical or Lean mismatch was found, so the
module and node were left unchanged; this independent reading is the only addition.
Server-only scompile.py compiled the delivered file cleanly in 1.4 seconds with
nice 19, two threads, and a 60-second limit.
