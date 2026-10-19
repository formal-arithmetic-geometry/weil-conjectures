## Worker report

The delivery states `AlgebraicGeometry.exists_flat_coordinate_chain` in
`Sheaf.AlgebraicGeometry.FlatCoordinateChain`. There is one theorem and its proof is
`sorry`; there are no new definitions, new nodes, dependency repairs, or statement
corrections. The node copy differs only in `lean`. The previous sandbox contained
only dispatcher briefs, so this is the first statement delivery, not a stage-1
handoff or a second reading.

Source checked directly: `literature/sga/SGA4-expose-18_reedition.pdf`, Exposé XVIII,
Lemmas 2.5 and 2.6, printed pp. 551–552 (PDF p. 53). Lemma 2.5 gives chains of
systems of parameters by induction in the three quotients; Lemma 2.6 realizes their
germs and adds the coordinate translation chains. The theorem's docstring records
the node's seven proof steps, including finite-type quasi-finiteness after shrinking
and exact endpoints when lifting quotient chains. No proof has been supplied.

The statement is rendered hypothesis by hypothesis and clause by clause as follows.

| Node text | Lean rendering |
| --- | --- |
| Algebraically closed field k | `{k : Type u} [Field k] [IsAlgClosed k]` |
| Integer d at least zero | `(d : ℕ)` |
| k-scheme X | `(X : Scheme.{u}) [X.Over (Spec (CommRingCat.of k))]` |
| Separated over k | `[IsSeparated (X ↘ Spec (CommRingCat.of k))]` |
| Finite type over k | `[LocallyOfFiniteType (X ↘ Spec (CommRingCat.of k))]` and `[QuasiCompact (X ↘ Spec (CommRingCat.of k))]`, the recorded definition's conjunction |
| Pure dimension d | `(hpure : X.IsPureDimension d)` |
| Every local ring has depth equal to its Krull dimension | `hCM : ∀ y : X, (IsLocalRing.depth (R := X.presheaf.stalk y) (X.presheaf.stalk y) : WithBot ℕ∞) = ringKrullDim (X.presheaf.stalk y)` |
| Maps u,v to affine d-space | `f g : X ⟶ 𝔸(ULift.{u} (Fin d); Spec (CommRingCat.of k))` |
| Both maps are k-morphisms | `[f.IsOver (Spec (CommRingCat.of k))]` and `[g.IsOver (Spec (CommRingCat.of k))]` |
| Quasi-finite maps, including finite type | `(hf : f.IsQuasiFinite) (hg : g.IsQuasiFinite)`, using the dependency's Stacks predicate |
| Flat maps | `[Flat f] [Flat g]` |
| Every closed point x | `(x : X) (hx : x ∈ closedPoints X)` |
| Open neighbourhood U of x | `∃ (U : X.Opens) (_hxU : x ∈ U), ...` |
| Integer r at least zero and maps w_0,...,w_r | `(r : ℕ)` and `w : Fin (r + 1) → (U.toScheme ⟶ 𝔸(ULift.{u} (Fin d); Spec (CommRingCat.of k)))` |
| All intermediate maps are k-morphisms | `∀ j, w j ≫ 𝔸(ULift.{u} (Fin d); Spec (CommRingCat.of k)) ↘ Spec (CommRingCat.of k) = U.ι ≫ X ↘ Spec (CommRingCat.of k)` |
| All intermediate maps are quasi-finite and flat | `∀ j, (w j).IsQuasiFinite ∧ Flat (w j)` |
| Exact first and last maps u restricted to U and v restricted to U | `w 0 = U.ι ≫ f ∧ w (Fin.last r) = U.ι ≫ g` |
| Consecutive pairs agree in all but at most one coordinate | For each `j : Fin r`, `Set.Subsingleton` of the indices `i` where `(w j.castSucc).appTop (AffineSpace.coord _ i) ≠ (w j.succ).appTop (AffineSpace.coord _ i)` |
| For d = 0 one may take r = 0 | The same existential witness additionally satisfies `d = 0 → r = 0` |

Depth has codomain `ℕ∞`, while ring Krull dimension has codomain `WithBot ℕ∞`;
the explicit coercion compares exactly these invariants. The CM assumption is made
at every point, without incorrectly requiring all stalks to have dimension d.
The self-module of every stalk is finite by its rank-one module instance, so depth
needs no additional finiteness assumption. The natural-number coordinate set is
lifted into the field/scheme universe, as required by Mathlib's affine-space API.
No universe parameter or implicit mathematical object is auto-bound; the file
explicitly declares `universe u` and all object binders.

Dependency declarations read and reused:

- `def-pc-scheme`: `Mathlib.AlgebraicGeometry.Scheme`,
  `AlgebraicGeometry.Scheme` and `AlgebraicGeometry.Scheme.Hom`.
- `def-weil-finite-type-morphism`: `Mathlib.AlgebraicGeometry.Morphisms.FiniteType`,
  `AlgebraicGeometry.LocallyOfFiniteType`, and
  `Mathlib.AlgebraicGeometry.Morphisms.QuasiCompact`, `AlgebraicGeometry.QuasiCompact`.
- `def-kun-topological-krull-dimension`: `Mathlib.Topology.KrullDimension`,
  `topologicalKrullDim`, used inside the recorded pure-dimension definition.
- `def-weil-pbc-depth`: `Sheaf.RingTheory.Depth`, `IsLocalRing.depth` and its
  underlying `Ideal.depth`.
- `def-weil-pbc-krull-dimension-ring`: `Mathlib.RingTheory.KrullDimension.Basic`,
  `ringKrullDim`.
- `def-sbc-affine-space`: `Mathlib.AlgebraicGeometry.AffineSpace`,
  `AlgebraicGeometry.AffineSpace`; coordinates use its existing
  `AlgebraicGeometry.AffineSpace.coord`, pulled back by `Scheme.Hom.appTop`.
- `pqf-def-quasifinite`: `Sheaf.AlgebraicGeometry.QuasiFiniteMorphism`,
  `AlgebraicGeometry.Scheme.Hom.IsQuasiFinite` (not Mathlib's predicate without
  the node's finite-type clause).
- `def-weil-flat-morphism`: `Mathlib.AlgebraicGeometry.Morphisms.Flat`,
  `AlgebraicGeometry.Flat`, equivalent to the stalkwise condition by
  `Flat.iff_flat_stalkMap`.
- `def-weil-pure-dimension`: `Sheaf.AlgebraicGeometry.PureDimension`,
  `AlgebraicGeometry.Scheme.IsPureDimension`.
- `def-weil-algebraic-closure`: `Mathlib.FieldTheory.IsAlgClosed.Basic`,
  `IsAlgClosed`; the node uses algebraic closedness, not a chosen algebraic closure.
- `def-weil-closed-points`: `Mathlib.Topology.JacobsonSpace`, `closedPoints`.
- `def-weil-proper-morphism`: `Mathlib.AlgebraicGeometry.Morphisms.Proper` exports
  `AlgebraicGeometry.IsSeparated` from `Morphisms.Separated`. Only separatedness
  is assumed, exactly as the statement asks; properness is not assumed.

The available non-Mathlib proof dependencies are imported without `public`:
`Sheaf.RingTheory.IsRegularOfDimensionDrop`,
`Sheaf.RingTheory.DepthQuotientNonzerodivisor`, and
`Sheaf.Topology.PresheafModuleStalkFunctor`. Their declarations are respectively
`RingTheory.Sequence.isRegular_of_dimension_drop`,
`IsLocalRing.depth_quotient_nonzerodivisor`, and
`PresheafOfModules.moduleStalkFunctor`. Other non-Mathlib proof dependencies have
no recorded statement yet and therefore add no imports. The Mathlib proof dependencies
are imported through `Mathlib.AlgebraicGeometry.AlgClosed.Basic`
(`AlgebraicGeometry.residueFieldIsoBase` and
`AlgebraicGeometry.SpecMap_residueFieldIsoBase_inv`),
`Mathlib.RingTheory.Ideal.AssociatedPrime.Finiteness`
(`associatedPrimes.finite`, also exporting
`biUnion_associatedPrimes_eq_zero_divisors`),
`Mathlib.RingTheory.Ideal.Operations` (`Ideal.subset_union_prime`),
and the already public finite-type module (`AlgebraicGeometry.locallyOfFiniteType_iff`).

Edge cases checked:

- The empty scheme satisfies pure dimension vacuously; there is no closed point to
  instantiate `x`, so the conclusion has no unintended nonempty hypothesis.
- When d = 0 the coordinate index is empty, the coordinate condition is vacuous,
  and `d = 0 → r = 0` requires a single vertex. `Fin.last 0` and the initial index
  both denote that vertex. Two k-morphisms to affine zero-space coincide by its
  canonical isomorphism with the base, so the endpoints are compatible.
- When d = 1, any two maps differ in at most one coordinate; a one-edge chain
  already meets the combinatorial condition.
- Equal charts can be joined with r = 0 in any dimension. The adjacent-edge index
  `Fin 0` is empty, and neither existence of a changed coordinate nor positive r
  is imposed.
- `Set.Subsingleton` allows zero changed coordinates as well as one, and covers all
  coordinates rather than a chosen partial coordinate list.
- Local rings have their own dimensions, including dimension zero at generic
  points; the depth equality does not force each to have dimension d.
- There is no restriction on the characteristic of k or on its universe.

Searches for an existing statement (all performed for this item through msearch.py):

- LeanFinder: `Two flat quasi-finite affine space charts on a Cohen Macaulay scheme
  are locally joined by a chain changing one coordinate at a time` — 8 hits,
  including affine-space finite-presentation, smooth-chart, and affine-transition
  results; none is a chain theorem.
- Loogle: `"AffineSpace", "chain"` — 0 hits.
- Mathlib grep: `coordinateChain|coordinate_chain|Cohen.?Macaulay|flat.*chain|chain.*flat`
  in `AlgebraicGeometry` — 0 hits.
- LeanSearch: `Finite chain of flat quasi finite morphisms to affine space differing
  in one coordinate` — 8 hits: quasi-finiteness/flatness predicates and finite or
  immersion instances; no chart-chain theorem.
- Direct `rg` of Mathlib for `flat_coordinate_chain|coordinateChain|coordinate_chain`
  — no hits.
- Direct `rg` of `WeilConjectures` and the project's `lean/Sheaf` for coordinate-chain
  spellings and chart-chain text — no matching theorem. Broader results were
  unrelated chain complexes, curve prime chains, or already recorded CM depth
  statements. Direct `grep -rn lem-pur-flat-coordinate-chain WeilConjectures`
  returned no hits.
- `dag/lean_names_upstream.json`: coordinate-chain and Cohen–Macaulay name patterns
  returned no match.

Validation: the delivered module compiled cleanly through
`scompile.py NM lem-pur-flat-coordinate-chain`, both as a sandbox module and under
its final library module name. No errors or warnings were reported. The source has
no line over 100 characters. The final delivery dry run returned `OK`: compilation and preflight passed except
for the independent second-reading section, which the second reader supplies; nothing
was pushed.

No statement dispute or prerequisite interface fault was found.


## Second reading by NM

I independently read the node, the complete statement module, each statement
 dependency's node and its recorded declaration, and SGA 4 Exposé XVIII 2.5–2.6
on PDF page 53 (printed pp. 551–552). The source is this PDF, not a Stacks
chain-of-charts lemma. The surrounding §2 has no blanket characteristic or
Noetherian-base assumption to add. Lemma 2.6 has a finite-type Cohen–Macaulay
scheme over an algebraically closed field and the two quasi-finite flat charts;
its proof uses the parameter-chain lemma 2.5 and then coordinate translations.
The node specializes this to separated, pure-dimensional X. I read the Lean
against that node, including those explicit hypotheses.

Independent object/hypothesis/conclusion checklist (all verdicts: exact):

1. Algebraically closed field k: `{k : Type u} [Field k] [IsAlgClosed k]`.
   Mathlib `IsAlgClosed` means polynomial splitting, equivalently a root for
   every nonconstant polynomial. No chosen closure or base subfield is imposed.
2. Nonnegative dimension d: `(d : ℕ)`. No positivity is imposed.
3. The k-scheme X: `(X : Scheme.{u})` and
   `[X.Over (Spec (CommRingCat.of k))]`; the same structure morphism is used
   everywhere via `X ↘ Spec (CommRingCat.of k)`.
4. Separatedness: `[IsSeparated (X ↘ Spec (CommRingCat.of k))]`, whose
   Mathlib field says the diagonal is a closed immersion. This does not ask
   that the structure map be proper.
5. Finite type: `LocallyOfFiniteType` and `QuasiCompact` instances on that
   structure morphism. These are the two clauses of the dependency node's
   definition, rather than local finite type alone.
6. Pure dimension d: `(hpure : X.IsPureDimension d)`. I opened the recorded
   `PureDimension.lean`: it quantifies over every irreducible component Z and
   says `topologicalKrullDim Z = (d : WithBot ℕ∞)`, with the subspace topology.
7. Cohen–Macaulay condition: `hCM` quantifies over every `y : X` and equates
   the depth of the self-module of `X.presheaf.stalk y` to its ring Krull
   dimension. I fetched the live `Sheaf.RingTheory.Depth` through
   `scompile.py --source`: `IsLocalRing.depth` is exactly maximal-ideal depth,
   and `Ideal.depth` is the supremum of regular-sequence lengths (infinity
   when IM = M). The stalk's self-module has the automatic finite-module
   instance. The coercion to `WithBot ℕ∞` compares the same two invariants;
   no extra local dimension d or depth bound is silently substituted.
8. The two ordered charts u,v: `(f g : X ⟶
   𝔸(ULift.{u} (Fin d); Spec (CommRingCat.of k)))`. I read Mathlib's
   `AffineSpace`, its first-projection `over`, and `coord`. This is the
   dependency's affine d-space, with exactly d standard coordinates.
9. Both charts are over k: the two `IsOver` instances enforce commutation
   with the fixed structure morphisms; arbitrary scheme maps are not used.
10. Quasi-finiteness and flatness of both charts: `hf`, `hg`, `[Flat f]`,
    `[Flat g]`. I fetched the current `QuasiFiniteMorphism` source: its
    `IsQuasiFinite` is local finite type AND quasi-compact AND isolation of
    every point in its scheme-theoretic fibre. Thus the node's finite-type
    clause is retained. Mathlib `Flat.iff_flat_stalkMap` identifies `Flat`
    with the node's stalkwise flatness condition.
11. Every closed point: `(x : X) (hx : x ∈ closedPoints X)`, before the
    existential witnesses. Mathlib's `closedPoints` is `IsClosed {x}`.
12. An open neighbourhood: `∃ (U : X.Opens) (_hxU : x ∈ U)`. No affine,
    compact, or nonempty-scheme assumption is added to the statement.
13. A finite nonempty sequence of maps: `(r : ℕ)` followed by
    `w : Fin (r + 1) → (U.toScheme ⟶ 𝔸(...))`. These are precisely
    w_0 through w_r, and the open neighbourhood may depend on x,f,g.
14. Every w_j is a k-morphism: the first universal clause equates its
    composite with the affine-space projection to `U.ι ≫ X ↘ Spec k`.
    This is the inherited k-structure on U, not a new arbitrary one.
15. Every w_j is quasi-finite and flat: the next universal clause is
    `(w j).IsQuasiFinite ∧ Flat (w j)`, with the same predicates as for f,g.
16. Exact endpoints: `w 0 = U.ι ≫ f` and
    `w (Fin.last r) = U.ι ≫ g`. These are morphism equalities, not merely
    equalities of germs or maps to the base.
17. Consecutive vertices differ in at most one coordinate: `∀ j : Fin r`,
    `Set.Subsingleton` of the set of i where the pullbacks of `coord ... i`
    along `w j.castSucc` and `w j.succ` differ. `Scheme.Hom.appTop` is the
    global-section pullback. Thus equality is equality of coordinate
    functions on U; the condition does not permit the exceptional coordinate
    to depend on a point of U. A subsingleton set has at most one element,
    and permits no change as well as one change.
18. Dimension zero: the same witnesses satisfy `d = 0 → r = 0`, exactly
    expressing that in this case a length-zero chain can be chosen.

Dependency and delivery audit: all twelve statement dependencies have a usable
recorded declaration or Mathlib match; I opened their signatures rather than
inferring their meaning from their names. The affine-space, algebraic-closure,
and closed-point nodes are Mathlib leaves with no `lean` record, and their
`mathlib_match` supplies the declarations used. The three project notions are
reused, without private definitions. I checked the current proof-dependency
records: the germ criterion still has no declaration to import; the stated
regular-sequence, quotient, depth, prime-avoidance, associated-prime,
closed-residue-field, finite-type and stalk tools are available through the
listed imports. There are no new nodes or dependency modules to audit and no
`statement_change` or citer audit is needed. The original node is unchanged
outside `lean`.

Edge cases checked independently:

- Empty X: there is no `x : X`, and the pure-dimension predicate itself permits
  the empty scheme. No nonemptiness assumption has been introduced.
- d = 0: `ULift (Fin 0)` and `Fin r` with r = 0 are empty; `Fin (r+1)` still
  has one vertex. Mathlib's affine-space projection is an isomorphism for an
  empty coordinate type, so two k-morphisms into it coincide. The endpoint
  equalities and the zero-edge conclusion are compatible.
- d = 1: the coordinate set has one element, so a direct edge satisfies the
  subsingleton condition. No unnecessary positive-length condition appears.
- f = g in any dimension: r = 0 is permitted. There is no demand that any
  coordinate actually change or that a changed coordinate exist.
- Zero-dimensional stalks are allowed and tested by their own ring dimension;
  the statement never requires all stalk dimensions to equal d. A zero ring
  is not silently substituted for a scheme stalk at a point.
- No characteristic restriction occurs. The arbitrary declared universe u
  supplies a common ambient universe for k, X, their section rings and all
  finite coordinate sets. `ULift.{u} (Fin d)` changes size encoding only,
  preserving the empty and singleton index cases. Every binder and universe
  is explicitly bound; there is no independent test-object universe.

Independent H4 searches, performed through the prescribed msearch wrapper:

- LeanFinder: `flat quasi-finite coordinate chain Cohen Macaulay` returned
  eight results about standard smooth presentations, flat going-down,
  finite flat modules, and transfer of a regular sequence along a flat map.
  I read the returned signatures; none connects two coordinate charts.
- LeanSearch: `Given two finite flat coordinate charts connect them locally
  through maps agreeing outside one coordinate` returned eight manifold
  coordinate-change results, none about schemes or flat quasi-finite charts.
- Loogle: `"AlgebraicGeometry.AffineSpace", "chain"` returned zero hits.
  An earlier unquoted `AffineSpace Flat` query was rejected for an unknown
  identifier, so that result was not treated as evidence of absence.
- Direct rg in Mathlib, upstream `WeilConjectures`, and project `lean/Sheaf`
  used `coordinate.?chain|chain.?coordinate|single.?coordinate` and
  `parameter.*(chain|replac)|chain.*parameter|chart.*chain|chain.*chart`.
  The matches were unrelated chain-complex coordinates, tensor-stalk
  complexes, or geometric dimension chains; there was no chart-chain theorem.
  I also searched `exists_flat_coordinate_chain` and the upstream-name table;
  no existing declaration was found. Search output is in `searches.jsonl`.

H5/H6/H8/H9 checks: the module has no definitions at all, no local notation or
instances, and exactly the named theorem with proof `sorry`. The module and
statement docstrings identify SGA XVIII 2.5–2.6 and the correct blueprint id.
The seven proof paragraphs follow the node's seven steps, including the
regular pivot on all three rings, exact endpoint repair when lifting quotient
chains, and finite type after common affine shrinking. I verified the signature
is verbatim equal to `lean.statement` and every source line has length at most
100. No mathematical or Lean mismatch was found. I left the Lean module and
node unchanged and added only this independent reading and its search evidence.

Validation: `python3 /home/ubuntu/weil-launcher-nt/scompile.py NM
lem-pur-flat-coordinate-chain lean/Sheaf/AlgebraicGeometry/FlatCoordinateChain.lean`
compiled the sandbox module and its final module name cleanly, with no errors
or warnings, under the default limit. Delivery dry run and delivery are performed
after this report is written.
