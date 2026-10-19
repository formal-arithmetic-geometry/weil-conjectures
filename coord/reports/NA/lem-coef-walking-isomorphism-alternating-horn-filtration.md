## Worker report

The module `Sheaf.AlgebraicTopology.WalkingIsomorphismAlternatingHornFiltration`
states `SSet.walking_isomorphism_alternating_horn_filtration`.  It imports
Mathlib's `CategoryTheory.WalkingIso`, `SSet.coherentIso` (the nerve of
`WalkingIso`), standard simplices, horns, subcomplexes, and `IsPushout`, together
with the recorded dependency module `Sheaf.CategoryTheory.EnhancedDiagramsCones`.
The proof is `sorry`, as required at stage 2; all data in the statement are
explicit and no definition uses `sorry`.

The dependency declaration used is
`Sheaf.CategoryTheory.EnhancedDiagramsCones`, declaration
`SSet.Enhanced.coneCategory`.  Its source docstring defines the enhanced
simplicial-set cone category and records the Mathlib simplicial-set conventions;
this item uses the same `SSet`, standard simplex, horn, and nerve objects.
The item does not restate that dependency's notion.

The node's common universe is the explicit Lean universe `u`; `coherentIso.{u}`
and every standard simplex and subcomplex use that universe.  The node's
filtration is indexed in Lean by `m` with `1 ≤ m`; this is the source index
`n = m + 1`, so it covers every stage `n ≥ 2` while avoiding a subtraction cast
in the face operator.

The Lean statement renders the node clause by clause as follows.

* `∃ (J : ℕ → coherentIso.Subcomplex) (hJ : Monotone J)` is the monotone
  sequence `J_1 ⊆ J_2 ⊆ ⋯` of simplicial subsets.
* `J 1 = Subcomplex.range (yonedaEquiv.symm coherentIso.hom.edge)` identifies
  `J_1` with the range of the forward `0 → 1` edge.  Mathlib's
  `coherentIso.hom` is the edge in the nerve of `WalkingIso`.
* `(⨆ n, J n) = ⊤` is the degreewise union/exhaustion of the nerve.
* For each `m ≥ 1`, `w : coherentIso _⦋m + 1⦌` is the forward alternating word;
  `w.obj j = if j.1 % 2 = 0 then WalkingIso.zero else WalkingIso.one` gives
  its alternating vertices.  The two membership clauses put `w` and its first
  face `coherentIso.δ 0 w` in the corresponding nondegenerate-simplex sets.
* The existential maps `a` and `b` and
  `IsPushout (Λ[m + 1, 0]).ι a b
  (Subcomplex.homOfLE (hJ (Nat.le_succ m)))` state that
  `J_m → J_(m+1)` is, with the displayed identifications, the pushout of the
  horn inclusion `Λ[m+1,0] → Δ[m+1]`.
* The two universal clauses say that the only new nondegenerate simplex in
  dimension `m+1` is `w`, and the only new one in dimension `m` is its first
  face `d₀w`.  Membership is compared in `coherentIso` through the canonical
  subcomplex inclusions; `Set.range ((J m).ι.app _)` is exactly the preceding
  stage in each degree.
* The final existential supplies `Jrev`, its monotonicity, initial value
  `Subcomplex.range (yonedaEquiv.symm coherentIso.inv.edge)`, top supremum, and
  the same pushout, alternating-word, and new-simplex clauses with the parity
  labels exchanged.  This is the reversed filtration beginning with `1 → 0`.

Before writing the statement I checked the edge cases `n = 2` (`m = 1`) and
`n = 3` by hand: the new words have dimensions 2 and 3, their interior faces
are degenerate, and `d₀ w_n` has dimension `n − 1`.  The initial range contains
both vertices and the forward edge, the supremum includes every degenerate
simplex through a nondegenerate alternating word, and swapping zero/one gives
the reverse construction.  The empty simplicial-set lifting cases do not arise
in this filtration statement; no nonemptiness hypothesis is added.

Searches for an existing declaration were made as follows.

* `msearch.py ... leanfinder "The nerve of the walking isomorphism admits a monotone alternating horn filtration by simplicial subcomplexes"` returned generic nerve/strict-Segal, standard-simplex, and generating-horn declarations; none states this filtration.
* `msearch.py ... loogle "WalkingIso, coherentIso, Subcomplex, horn.ι, IsPushout"` returned no usable result (`WalkingIso` is not in the Loogle identifier namespace).
* `msearch.py ... grep "WalkingIso|coherentIso|alternating.*horn|IsPushout"` found generic `IsPushout` uses and the Mathlib coherent-isomorphism file, but no alternating filtration theorem.
* `rg` over `WeilConjectures/` and the repository `lean/Sheaf/` found no declaration of this item; the DAG search found only this node and its reviewed citer.

The returned delivery's appended `mathlib_searches` rows were not copied;
the node copy retains the repository's original stage-1 `mathlib_searches` field
unchanged.  The missing module, lean record, and report were supplied here.
No `STATEMENT-DISPUTED:` flag or node fault remains.

## Second reading by NA

I reread the repaired node, its complete theorem signature, and the full source
of the dependency declaration.  The Lean signature binds the sequence, its
monotonicity, the forward initial range, exhaustion, every stage map, and the
reversed sequence explicitly.  The stage reindex `m ≥ 1` is equivalent to the
node's `n ≥ 2`; the parity condition gives exactly the forward alternating word,
and the second branch gives the corresponding reversed word.  The order of the
four `IsPushout` maps is the Mathlib order
`IsPushout (horn inclusion) (horn-to-previous-stage) (simplex-to-new-stage)
(previous-to-new-stage)`.  The two universal difference clauses identify
precisely `w_n` and `d₀w_n`, while the reversed filtration repeats all of those
clauses after exchanging the two vertices.  No mismatch between the node and
Lean was found, and the stage-2 compile completed for the sandbox and library
forms of the module.
