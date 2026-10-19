## Worker report

Item: `lem-coef-infinity-comma-equivalence-invariance`, group Q30, stage 2.

The module `Sheaf.CategoryTheory.CoherentOrientedFiberProductInvariance` states
`SSet.Enhanced.coherentOrientedFiberProduct_equivalence_invariance` with `sorry`.
Its three construction helpers implement exactly the objects and induced map introduced
in the item's statement; all their data are explicit. There are no additional postponed
helper theorems, dependency repairs, new nodes or statement corrections.

Source read: Kerodon Remark the project server, https://kerodon.net/tag/03PN, whose displayed
commutative diagram has three equivalences and whose conclusion is equivalence of the
induced oriented fiber products. It identifies the proof as applying Corollary the project server
to the arrow/endpoints/source-product diagram. The record also cites Definition the project server
(01KF); two attempts to retrieve that tag timed out. The complete degreewise construction
is explicit in our node and the recorded enhanced-diagram dependency. No disagreement
with the source was found. The theorem docstring carries all eight DAG proof steps,
including the factorization through S and U and the strict coordinate identifications.

Hypothesis and clause correspondence:

- A fixed containing universe: explicitly bound `universe u` and
  `{C D B C' D' B' : SSet.{u}}`. There is no smaller-universe bound on the inputs.
  `set_option autoImplicit false` forbids implicit auto-binding.
- Six quasicategories: the six explicit `[Quasicategory ...]` binders, one per input.
- Four functors F, G, F', G': the four simplicial-map binders with exactly the
  source/target types in the node.
- Three comparison functors: `v : C ⟶ C'`, `w : D ⟶ D'`, `h : B ⟶ B'`.
- Three equivalence hypotheses: `hv : IsFunctorEquivalence v`,
  `hw : IsFunctorEquivalence w`, `hh : IsFunctorEquivalence h`. This is the
  dependency's quasi-inverse/coherent-natural-equivalence predicate, not an ordinary
  categorical equivalence or an arbitrary equivalence of underlying types.
- Exact square equations hF = F'v and hG = G'w:
  `hF : F ≫ h = v ≫ F'` and `hG : G ≫ h = w ≫ G'`.
- T and T': `coherentOrientedFiberProduct F G` and
  `coherentOrientedFiberProduct F' G'`. Its data are Mathlib's pullback of
  `F ⊗ₘ G : C ⊗ D ⟶ B ⊗ B` and the joint endpoint map from
  `(ihom Δ[1]).obj B`. The latter is `lift` of the existing `evaluation` at
  vertices 0 and 1. In degree n this is a pair `((c,d),eta)` satisfying
  `eta|0 = F(c)` and `eta|1 = G(d)`, exactly the node's iterated degreewise
  pullback with reordered coordinates. The full simplex endpoint equalities are
  retained. No vertex-only approximation is made.
- Canonical comparison: `coherentOrientedFiberProductMap F G F' G' v w h hF hG`
  uses `pullback.map` with `(v ⊗ₘ w)` on the object pair,
  `((ihom Δ[1]).map h)` on the entire coherent arrow, and `h ⊗ₘ h` on
  the base. Thus its formula is exactly `(c,eta,d) ↦ (v(c),h(eta),w(d))`
  in every degree. Both compatibility proofs are structural calculations in this
  definition; its data do not come from a choice or an unproved existence theorem.
- The first two conjuncts assert `Quasicategory` of T and T' separately.
- The third conjunct asserts `IsFunctorEquivalence` of that specified comparison.
- The last two conjuncts assert exact equalities of simplicial maps to C' and D'.
  `coherentOrientedFiberProductObjects` is the pullback projection to C times D;
  its composition with the cartesian `fst` and `snd` gives precisely each endpoint
  projection, on both sides of the two equalities.
- No fibration assumption on F, G, F' or G' occurs in any binder. No `Nonempty`
  assumption or selected vertex occurs. The point-target case is a specialization
  with `D = D' = Δ[0]`, `w = 𝟙 _`, `G' = G ≫ h` and `hG` the identity
  composition equality. G is any map from that point, without an image-membership
  premise for F; no additional conjunct is needed to express this specialization.

Dependency declarations used:

- `Sheaf.CategoryTheory.EnhancedDiagramsCones` (public import):
  `SSet.Enhanced.evaluation`, `SSet.Enhanced.IsFunctorEquivalence`, and the internal
  coherent-equivalence conventions `AreNaturallyEquivalent`, `diagramVertex` and
  `IsEquivalenceEdge` used by that predicate. Read the full signatures and docstrings.
  Simplicial sets, quasicategories, internal hom and cartesian product are Mathlib's
  existing `SSet`, `SSet.Quasicategory`, `ihom` and tensor in its cartesian structure.
- The stated proof dependencies are imported, without `public`, exactly as prescribed:
  `Sheaf.CategoryTheory.IsofibrationExponentiation`
  (`SSet.Enhanced.isofibration_exponentiation`, `IsIsofibration`),
  `Sheaf.CategoryTheory.IsofibrationPullbackEquivalence`
  (`SSet.Enhanced.isofibration_pullback_equivalence`),
  `Sheaf.AlgebraicTopology.JoyalQuasicategoryCharacterizations`
  (`SSet.joyal_quasicategory_characterizations`),
  `Sheaf.AlgebraicTopology.JoyalModelStructure`
  (`SSet.exists_joyal_model_structure`),
  `Sheaf.CategoryTheory.IsofibrationBaseChange`
  (`SSet.Enhanced.isofibration_base_change`). Their full declarations and proof
  docstrings were read; they are the inputs used in the eight-step proof plan.
- `Mathlib`'s `CategoryTheory.Limits.pullback`, `pullback.fst`, `pullback.map`,
  `CategoryTheory.CartesianMonoidalCategory.lift`, `fst`, `snd` and
  `CategoryTheory.MonoidalCategory.tensorHom_comp_tensorHom` supply the actual
  constructions and their structural compatibility.

Edge cases checked before writing:

- Empty C or D gives an empty degreewise product and hence empty T; the theorem
  never requests a vertex. Empty B forces the existence of F and G to restrict
  their sources accordingly. Inner-horn conditions on empty simplicial sets are
  vacuous, and equivalence hypotheses do not force unrelated sources inhabited.
- Identity vertical functors give the expected identity comparison, including for
  empty T. The compatibility proofs do not require F or G to lift any horn.
- Take B = nerve([1]), C = D = Δ[0], F selecting 0 and G selecting 1.
  The arrow 0 to 1 exists though 1 is not in the image of F. The comparison for
  identity vertical functors is covered with no extra premise. Reversing the
  endpoints produces an empty arrow pullback, also allowed.
- For discrete B, only equal endpoints admit arrows, and the same construction
  reduces to the expected matching-object pullback. For nerves of ordinary
  categories it retains the entire usual comma nerve, including noninvertible arrows.
- Vertices 0 and 1 are in the required order: the arrow starts at F(c) and ends
  at G(d). The two conclusion equations project onto the v and w coordinates,
  respectively; they assert strict equality rather than natural equivalence.

Searches for an existing declaration:

- `msearch.py ... leanfinder` query "Compatible equivalences of quasicategories
  induce equivalences on coherent oriented fiber products of arrow functor
  categories": eight hits, chiefly Cech nerve equivalences, ordinary costructured
  arrows, and nerve/product comparisons; no quasicategorical oriented-product theorem.
- `msearch.py ... loogle '"Comma", "isEquivalence"'`: six hits including
  `CategoryTheory.Comma.isEquivalenceMap`, `isEquivalence_preLeft`,
  `isEquivalence_preRight`, `isEquivalence_post` and two finite-etale results.
  Read Comma/Basic.lean around the full isEquivalenceMap instance and its projection
  equations. Its inputs are ordinary categories and natural isomorphisms; it is
  not the statement about internal arrow quasicategories.
- `msearch.py ... grep 'comma|Quasicategory|IsFunctorEquivalence'
  AlgebraicTopology/Quasicategory`: 25 hits, concerning quasicategory definitions,
  nerves, strict Segal objects and inner fibrations, with no matching theorem.
- `rg` through the upstream `WeilConjectures` for the item id found no occurrence;
  searches for `IsFunctorEquivalence`, oriented-product and comma constructions
  found no matching upstream quasicategorical theorem.
- `rg` through `lean/Sheaf` found the recorded enhanced notions and the
  proof dependencies. The existing file `InfinityCommaEquivalenceInvariance.lean`
  belongs to `lem-coef-infinity-cofinal-colimit-restriction`; its declarations
  assert weak contractibility of incoming commas, not this general equivalence.
  Read that module in full. Other oriented-product hits concern topoi, not this
  quasicategorical construction. No usable general construction or theorem found.
- Exact name searches for `coherentOrientedFiberProduct` and `orientedFiberProduct`
  in Mathlib, upstream and `lean/Sheaf`, and in `dag/lean_names_upstream.json`,
  found no collision. No repair note for this item exists in `coord/repair-notes`.

Only the item's `lean` field changes in the copied JSON; its mathematical statement,
statement dependencies and proof remain verbatim. All four declarations have owning-node
source docstrings. The only postponed theorem is the item's theorem.

Validation: the prescribed `scompile.py Q30
lem-coef-infinity-comma-equivalence-invariance <module>` returned exit code 0.
Its sandbox check took 36.4 seconds and its library-path check took 6.4 seconds;
there were no errors or warnings. No global build or direct compilation was run.
The source has no lines exceeding 100 characters. A local field comparison confirmed
that the JSON differs from the read-only node only in `lean`.

The required `deliver2.py ... --no-push` returned
`OK (dry run): commit 6371959474 passes the preflight and compiles; nothing pushed`.
The final module documentation also lists all construction helpers and the main statement.
The delivery wrapper supplies the notice that the maintainer performs the independent
review; no worker second reading is claimed.

## Second reading by Q30

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
