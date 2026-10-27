## Worker report

The module `Sheaf.AlgebraicGeometry.StratificationGenericNeighborhood` states
`AlgebraicGeometry.Scheme.exists_stratification_generic_neighborhoods` with one `sorry`.
It introduces no definitions and changes only the item's `lean` field. All variables and
universes are explicit (`set_option autoImplicit false`, `universe u`).

The node is a scheme-theoretic generic-neighborhood lemma, not a coefficient assertion:
there is no sheaf or coefficient hypothesis to add. Its source is the final curve clause
of main-20261015 `sk-lem-coefficient-heart/_section.md`; the proof.md stops after part (3).
The source proof supporting this refinement is the six-step DAG proof. I also read
Stacks `schemes.tex`, labels `lemma-open-fibre-product` (01JR),
`lemma-base-change-immersion` (01JY), and `lemma-immersion-when-closed` (01IQ).

Hypotheses and clauses, individually matched:

- A scheme X with no dimension or reducedness restriction is `(X : Scheme.{u})`.
- Locally Noetherian is `[IsLocallyNoetherian X]`; quasi-compact is `[CompactSpace X]`.
  These are precisely the two parts of Noetherian in the node, without imposing
  any separation assumption.
- The finite locally closed stratification, its pairwise disjoint covering, and its
  actual scheme immersions are `(s : FiniteLocallyClosedStratification X)` from the
  dependency's recorded declaration. The fields are `n`, `stratum`,
  `isLocallyClosed_stratum`, `iUnion_stratum_eq_univ`, `pairwise_disjoint_stratum`,
  `domain`, `immersion`, `isImmersion`, and `range_immersion`. Indexing with `Fin s.n`
  is the reindexing of 1,...,m by 0,...,m-1 and permits m=0.
- Finitely many irreducible components is `(irreducibleComponents X).Finite`.
  The family index `irreducibleComponents X` is the subtype of component subsets.
- The generic point family is `η : irreducibleComponents X → X`.
  `IsGenericPoint (η C) C.val` asserts its defining closure equality and therefore
  membership in C. `∀ x : X, IsGenericPoint x C.val → x = η C` asserts uniqueness.
- The stratum index family is `j : irreducibleComponents X → Fin s.n`.
  `η C ∈ Set.range (s.immersion (j C))` asserts the selected stratum contains it;
  `∀ k : Fin s.n, η C ∈ Set.range (s.immersion k) → k = j C` asserts uniqueness.
- The open neighborhoods are `W : irreducibleComponents X → X.Opens`, with
  `η C ∈ W C` and `(W C : Set X) ⊆ Set.range (s.immersion (j C))`.
  `X.Opens` carries the open subscheme structure and `(W C).ι` is its inclusion.
- The actual T_C is the domain of
  `pullback.fst (W C).ι (s.immersion (j C))`, namely
  `pullback (W C).ι (s.immersion (j C))`. Its factors are exactly W_C and the given
  `s.domain (j C)`, over X. No replacement by reduced subschemes occurs.
- Its first projection t_C has the two separate conclusions `Surjective (...)` and
  `IsClosedImmersion (...)` on that exact `pullback.fst`.
- Its second projection q_C is `pullback.snd (W C).ι (s.immersion (j C))`, with
  conclusion `IsOpenImmersion (...)`.
- The union U is `(⨆ C, W C : X.Opens)`. In `X.Opens` its underlying set is the union
  of the underlying sets of W_C, and it is open by its type. Its density is
  `Dense ((⨆ C, W C : X.Opens) : Set X)`. The last conjunct says
  `∀ C : irreducibleComponents X, η C ∈ (⨆ D, W D : X.Opens)`.
- When X is empty, no component is irreducible because irreducibility includes
  nonemptiness. Thus the family is empty, and its supremum is the empty open,
  equal to the whole empty X. Its density is valid. The same formula handles
  this case; no nonemptiness binder is present.
- No factorization W_C → S_j is asserted. No integrality, irreducibility,
  reducedness, curve hypothesis, or fixed positive number of strata is imposed.

Dependency declarations read and used:

- `Sheaf.AlgebraicGeometry.FiniteLocallyClosedStratification`:
  `Topology.FiniteLocallyClosedStratification` and
  `AlgebraicGeometry.Scheme.FiniteLocallyClosedStratification`. I use the recorded
  interface, not upstream `Scheme.Stratification`, which adds constructibility.
- `Mathlib.Topology.Irreducible`: `irreducibleComponents` (maximal irreducible subsets).
- `Mathlib.Topology.Sober`: `IsGenericPoint` (closure of a singleton).
- `Mathlib.CategoryTheory.Limits.Shapes.Pullback.HasPullback`:
  `CategoryTheory.Limits.pullback`, `pullback.fst`, `pullback.snd`.
- `Mathlib.AlgebraicGeometry.Morphisms.ClosedImmersion`:
  `AlgebraicGeometry.IsClosedImmersion`.
- `Mathlib.AlgebraicGeometry.OpenImmersion`: `AlgebraicGeometry.IsOpenImmersion`.
- `Mathlib.AlgebraicGeometry.Morphisms.UnderlyingMap`: `AlgebraicGeometry.Surjective`.
- `Mathlib.AlgebraicGeometry.Noetherian`: `AlgebraicGeometry.IsLocallyNoetherian`;
  the defining class `IsNoetherian` was also read to confirm the two assumptions.
- `Mathlib.Topology.Defs.Filter`: `CompactSpace`, available through the Noetherian
  import, is the recorded quasi-compactness notion and requires no Hausdorff property.

The proof-plan imports include the recorded Mathlib modules for all proof dependencies:
`Noetherian` (finite components), `Properties` and `Sober` (sobriety and generic-point
uniqueness), `Irreducible` (component cover), `Restrict`
(`isPullback_morphismRestrict`), `Morphisms.Immersion` (base change of immersions),
and `Morphisms.ClosedImmersion` (`IsClosedImmersion.iff_isPreimmersion` and
`of_isPreimmersion`). Their signatures and source docstrings were read. Modules that
also provide statement notions are public imports; the remaining proof imports are plain.
No proof import was omitted for a cycle.

Edge cases checked mathematically before writing:

- Empty X and zero strata: the empty families exist and the empty union is X, dense.
- Empty strata in a nonempty stratification never receive a generic-point index.
- X=Spec(k[ε]/ε²) and the single stratum Spec(k): W=X is allowed; t is the
  surjective closed immersion Spec(k)→Spec(k[ε]/ε²), not an isomorphism. This tests
  retention of nilpotents and the deliberate absence of a W→stratum factorization.
- Two crossing irreducible components: removing the other component leaves an open
  containing the chosen generic point, even though the component itself is not open.
- One stratum may contain several component generic points: j need not be injective.
- A proper locally closed stratum through a generic point only has to contain the
  chosen neighborhood, not every point of that component.
- The single stratum X with its identity immersion allows W=X; no hidden properness
  or positive-dimension condition occurs. All characteristics are allowed.

Searches actually run (2026-10-22):

- `msearch.py leanfinder`: "A finite locally closed stratification of a Noetherian
  scheme has open neighborhoods of each irreducible component generic point contained
  in its stratum, whose stratum pullbacks are surjective closed immersions".
  Eight hits: finite components, `genericPoints.component_surjective`,
  `genericPoint_eq_of_isOpenImmersion`, scheme sobriety, and Noetherian open-subset
  lemmas. None states the combined neighborhood and scheme-pullback assertion.
- `msearch.py leansearch`: "For a finite locally closed stratification of a Noetherian
  scheme, every irreducible component generic point has an open neighborhood contained
  in its stratum image". Eight hits, mostly `genericPoints` and its component interface,
  and finite irreducible components; no full match.
- `msearch.py loogle`: `AlgebraicGeometry.IsImmersion, IsGenericPoint`: zero hits.
- `msearch.py grep`: `genericPoints|isClosedImmersion.*[Rr]ange|[Ss]tratification`
  in `AlgebraicGeometry`: five hits, four on diagonals and one on
  `IsClosedImmersion.iff_isPreimmersion`; no full match.
- `rg` in both project roots for `generic.*[Ss]trati|[Ss]trati.*generic`,
  `generic_neighborhood|genericNeighborhood|generic_neighbourhood` found related
  generic lissity and finite generic-fibre results. I read
  `WeilConjectures/AlgebraicGeometry/FiniteGenericFiberStratumInteriors.lean` and
  `WeilConjectures/WeilSheaf/LisseLocus.lean`: the former assumes a finite map to an
  integral affine base and states only a subset of stratum interiors; the latter
  states lissity with additional reducedness and coefficient hypotheses. Neither
  states this item. `grep -rn` for the exact node id in `lean/WeilConjectures` had
  no hits. The upstream-name index search for generic/stratification had no hits.
- Direct source searches of the relevant Mathlib declarations confirmed all the
  dependency notions above are reused rather than copied.

Validation: the prescribed `scompile.py` compiled the file as both a sandbox module
and its intended library module without errors or warnings. The final delivery dry
run and push run repeat the per-file compile and run the server preflight.

There are no node faults, statement disputes, new nodes, or dependency modules.

## Second reading by Q57

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
