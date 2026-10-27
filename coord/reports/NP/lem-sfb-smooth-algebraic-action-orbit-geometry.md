## Worker report

The module `Sheaf.AlgebraicGeometry.SmoothAlgebraicActionOrbitGeometry` states
`AlgebraicGeometry.smooth_algebraic_action_orbit_geometry`, with one postponed theorem
and the real helper construction `SmoothAlgebraicAction.orbitMap`. There are no new
nodes, dependency repairs, or changes to the natural-language node. The helper is
exactly the orbit map already introduced in this item's statement, not an independent
notion. No scheme or map is defined by choosing from the postponed theorem.

Read the item's statement, all twelve proof steps, all twelve statement-dependency
records, and their used declarations and docstrings. Read Milne's PDF at Propositions
1.65(b),(c), 7.4(b), 7.5, the isotropy paragraph, 7.6, and Appendix A.11, A.14--A.15,
A.71--A.73. Appendix A.11 defines algebraic schemes by finite affine covers and does
not add separatedness. The statement keeps this scope. The proof docstring reproduces
the twelve steps and their dependency citations, including the disconnected-group
and nonreduced-stabilizer arguments. All recorded proof-dependency modules are imported
without `public`; statement APIs are public imports.

Hypothesis and clause audit:

| Node phrase | Lean rendering |
| --- | --- |
| Algebraically closed field F | `{F : Type u} [Field F] [IsAlgClosed F]` |
| Group scheme G over F | `G : Over (Spec (.of F))` with `[GrpObj G]` |
| G smooth and finite type | `[Smooth G.hom]`, `[LocallyOfFiniteType G.hom]`, `[QuasiCompact G.hom]` |
| Finite-type F-scheme X | `X : Over (Spec (.of F))`, `[LocallyOfFiniteType X.hom]`, `[QuasiCompact X.hom]` |
| Morphism action with unit and multiplication identities | `[ModObj G X]`; its `smul`, `one_smul`, and `mul_smul` are precisely these data and identities |
| Rational point x | `x : 𝟙_ (Over (Spec (.of F))) ⟶ X`; the tensor unit is Spec F over itself |
| Orbit map g ↦ gx | `orbitMap x := lift (𝟙 G) (toUnit G ≫ x) ≫ ModObj.smul (M := G) (X := X)` |
| Full stabilizer fibre product | `pullback (orbitMap (G := G) x) x` in the over category, whose underlying scheme is the stated scheme fibre product; no reduction |
| Closed finite-type subgroup scheme | Existential `GrpObj` on this actual pullback, `IsClosedSubgroupScheme (pullback.fst ...)`, and `LocallyOfFiniteType` plus `QuasiCompact` of its structure map |
| Image support locally closed | `IsLocallyClosed (Set.range (orbitMap ...).left)` |
| Reduced induced orbit | Existential family `O x`, immersion `i x`, `IsReduced (O x).left`, and equality of its image with that orbit support |
| Canonical reduced structure in every suitable open | For every open `U` containing the support, and every proof that its inverse image is closed, a unique isomorphism with `(vanishingIdeal ⟨U.ι ⁻¹' support, hclosed⟩).subscheme`, commuting with its immersion and `U.ι` |
| Orbit smooth and finite type | `Smooth (O x).hom`, `LocallyOfFiniteType (O x).hom`, `QuasiCompact (O x).hom` |
| Orbit stable under G | A `ModObj G (O x)` for which `IsModHom G (i x)` |
| Factorization through flat surjective lfp beta | `β x ≫ i x = orbitMap ...`, `Flat (β x).left`, `Surjective (β x).left`, `LocallyOfFinitePresentation (β x).left` |
| Every geometric fibre is a stabilizer translate | For every algebraically closed extension E/F and point `q : Spec E ⟶ O x`, a lift `h` of q and an isomorphism `G_x ⊗ Spec E ≅ pullback (β x) q`. Its second projection is the base projection; its first projection is multiplication of h with the stabilizer inclusion, explicitly specifying left translation |
| Extension-point notation | `t` is quantified with the equation `t = Over.mk (Spec.map (CommRingCat.ofHom (algebraMap F E)))`; it cannot be an arbitrary test scheme. The equality is a presentation of the fixed Spec E, not an extra mathematical restriction |
| Transitivity over every algebraically closed extension | For all E/F and all `p q : Spec E ⟶ O x`, `∃ g, g • (p ≫ i x) = q ≫ i x`, using the original action on X |
| O_x(F) partition X(F) | The image on rational points is `MulAction.orbit (Spec F ⟶ G) x`; every rational point is in some image. Group orbits form a partition. Supports additionally either agree or are `Disjoint`, which also gives the required disjointness on rational points |
| Equidimensional orbit | Every `C ∈ irreducibleComponents (O x).left` has dimension `topologicalKrullDim (O x).left` |
| Dimension formula | `dim G = dim G_x + dim O_x` in `WithBot ℕ∞`. These are finite nonnegative dimensions of nonempty finite-type schemes, so this is exactly the rearrangement of the node's subtraction formula |
| Closure and boundary invariant | For either `T = closure support` or `T = closure support \ support`, the full action sends the preimage under the second projection into T. In addition, a reduced closed immersion with image T carries a compatible `ModObj` action. Uniqueness of reduced closed structures makes this the canonical reduced closure or boundary |
| Boundary orbits smaller | For every rational y whose entire orbit support is in the boundary, `topologicalKrullDim (O y).left < topologicalKrullDim (O x).left` |
| Connected G implies irreducible orbit | `ConnectedSpace G.left → IrreducibleSpace (O x).left` |
| No extra affineness, separation, reducedness, connectedness | None occur as hypotheses. In particular, `GrpObj` is on the category of all schemes over Spec F; `IsClosedSubgroupScheme` does not assert reducedness or smoothness of the stabilizer |

The existential family expresses existence of the canonical orbit subschemes;
canonicity is the explicit unique-isomorphism clause. No subsequent definition
extracts arbitrary data from this theorem's `sorry`. Pullbacks and products in
`Over (Spec F)` are the standard scheme fibre products. Scheme and coefficient
objects use the project's fixed universe `u`, including every field extension in
that universe, as in sibling scheme-action statements. The group operations and
action on Hom sets are the canonical existing Mathlib operations, not hypotheses
about a separate abstract action.

Dependency declarations used:

- `def-weil-field`: `Field`, Mathlib.Algebra.Field.Defs; `def-weil-algebraic-closure`:
  `IsAlgClosed`, Mathlib.FieldTheory.IsAlgClosed.Basic (the record points to
  AlgebraicClosure and explicitly names IsAlgClosed for the algebraically closed notion).
- `def-sc-group-scheme`: `CategoryTheory.GrpObj`, Mathlib.CategoryTheory.Monoidal.Grp;
  the documented over-scheme specialization and `AlgebraicGeometry.IsClosedSubgroupScheme`
  are in WeilConjectures.AlgebraicGeometry.GroupScheme.Defs.
- `def-sbc-smooth-morphisms`: `AlgebraicGeometry.Smooth`,
  Mathlib.AlgebraicGeometry.Morphisms.Smooth.
- `def-weil-finite-type-morphism`: `AlgebraicGeometry.LocallyOfFiniteType` and
  `AlgebraicGeometry.QuasiCompact`, Mathlib.AlgebraicGeometry.Morphisms.FiniteType
  and Mathlib.AlgebraicGeometry.Morphisms.QuasiCompact.
- `def-pc-scheme`: `AlgebraicGeometry.Scheme` and its Hom type,
  Mathlib.AlgebraicGeometry.Scheme.
- `def-pc-fibre-product`: `CategoryTheory.Limits.pullback`, `pullback.fst`,
  `pullback.snd`, Mathlib.CategoryTheory.Limits.Shapes.Pullback.HasPullback;
  the over-category cartesian structure uses these exact pullbacks.
- `lem-weil-pbc-reduced-induced-closed-subscheme`:
  `Scheme.IdealSheafData.reduced_induced_closed_subscheme`,
  WeilConjectures.AlgebraicGeometry.ReducedInducedClosedSubscheme, with the actual
  `vanishingIdeal`, `subscheme`, and `subschemeι` appearing in the signature.
- `def-weil-flat-morphism`: `AlgebraicGeometry.Flat`,
  Mathlib.AlgebraicGeometry.Morphisms.Flat.
- `def-sbc-locally-finite-presentation`: `AlgebraicGeometry.LocallyOfFinitePresentation`,
  Mathlib.AlgebraicGeometry.Morphisms.FinitePresentation.
- `def-kun-topological-krull-dimension`: `topologicalKrullDim`,
  Mathlib.Topology.KrullDimension, with `irreducibleComponents` from the topology API.
- `def-weil-connected-scheme`: `ConnectedSpace`, Mathlib.Topology.Connected.Basic.
- The action uses Mathlib.CategoryTheory.Monoidal.Cartesian.Mod's `ModObj` and
  canonical Hom-set `MulAction`; `IsModHom` expresses invariance of the inclusions.

Edge cases checked before drafting: X may be empty (then no x, and the asserted
families and point clauses are empty); each existing x has a nonempty orbit and
stabilizer (identity supplies points). G may be disconnected or nonaffine, X may
be nonseparated or nonreduced. A trivial action gives a point orbit and the whole
G as stabilizer. A transitive action has empty boundary; boundary dimension
inequalities quantify over no contained orbits in that case. A zero-dimensional
orbit likewise has empty boundary. Frobenius-type actions in characteristic p
can have nonreduced stabilizers; the pullback and fibre isomorphism retain them,
and beta is asserted flat and lfp, never smooth. No integrality assumption is
imposed on the orbit for the generic-flatness proof, and connectedness is used
only for the last implication.

Searches actually run with msearch.py:

- LeanSearch: `smooth algebraic group action orbit locally closed scheme stabilizer`.
  Eight hits concerning abstract group actions, including `MulAction.stabilizer`,
  `MulAction.ofQuotientStabilizer_mem_orbit`, `MulAction.index_stabilizer`, and
  `MulAction.IsFixedBlock.orbit`; none states the scheme orbit theorem.
- LeanFinder: `smooth finite type group scheme action orbit locally closed stabilizer dimension`.
  Eight hits, including `stabilizer_isOpen`, `ProperlyDiscontinuousSMul.finite_stabilizer`,
  `MulAction.index_stabilizer`, and finite cardinal orbit-stabilizer results. No match.
- Loogle: `CategoryTheory.ModObj, CategoryTheory.GrpObj` gave no hits;
  `CategoryTheory.ModObj` gave the existing action class and related constructors,
  action map, `IsModHom`, and trivial/regular action APIs. Reused those definitions.
- Mathlib grep: `orbit|stabilizer|equidimensional`, subdirectory AlgebraicGeometry:
  seven hits in elliptic-curve orbit constructions and an algebraic-cycle comment,
  no algebraic group orbit theorem.
- Direct rg of `orbitMap|orbit_map|IsEquidimensional|equidimensional` and
  `Orbit|orbit|MulAction|Action|Stabilizer|stabilizer` in the project's
  WeilConjectures/AlgebraicGeometry and Sheaf/AlgebraicGeometry: existing specific
  quotient and GIT actions, no theorem or orbit-map construction matching this item.
  GroupSchemeLinearization has a general equalizer stabilizer; this statement uses
  the requested actual fibre product directly and defines no second stabilizer.
- Direct rg for the exact item id in WeilConjectures, Sheaf, and
  dag/lean_names_upstream.json: no existing declaration. Checked the full signatures
  of GrpObj, ModObj, Hom action, the over-category product, the reduced induced
  closed-subscheme theorem, IsImmersion, and the dimension API before using them.

No `STATEMENT-DISPUTED` issue or source-based correction was needed. The initial
compile exposed unresolved group arguments on the orbit map; these were supplied
explicitly. The author's clause audit strengthened the draft's closure/boundary
clause from support invariance alone to also exhibit their invariant reduced
closed scheme structures. No node statement changed.

Validation: every compilation is through the prescribed `scompile.py` wrapper;
no build or direct compilation of the shared library was run. Final compile and
delivery preflight results are recorded below when complete.

Final validation: the complete current module compiled cleanly through scompile.py
in both the sandbox and library-path checks, with no errors or warnings. All lines
are at most 100 characters. `deliver2.py --no-push` returned
`OK (dry run): commit 64889b03a36 passes the preflight and compiles; nothing pushed`.
The packet contains exactly the module, the item's lean-only node record, and this
report. The maintainer performs the independent review; no worker second reading
is claimed.

## Second reading by NP

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.

## Maintainer review fix (independent reader, 2026-10-25)

The stabilizer clause used `AlgebraicGeometry.IsClosedSubgroupScheme`, a declaration of the DAG
node `def-sc-group-scheme-subgroup`, which is not in the item's `stmt_deps` (H2). It is replaced
by the equivalent inline `IsMonHom (pullback.fst …) ∧ IsClosedImmersion (pullback.fst …).left`:
`IsClosedSubgroupScheme` is `IsMonHom` plus injectivity on `R`-points plus a closed immersion,
and a closed immersion is a monomorphism, so injectivity on points is automatic. The import
`WeilConjectures.AlgebraicGeometry.GroupScheme.Defs`, then unused, is replaced by the Mathlib
imports `Monoidal.Cartesian.Grp` and `Monoidal.Cartesian.Over`. No other change. The fixed module
compiles cleanly (nt_compile, 21 s).
