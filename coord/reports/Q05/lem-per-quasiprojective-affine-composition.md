## Worker report

The module `Sheaf.AlgebraicGeometry.QuasiprojectiveAffineComposition` states
`AlgebraicGeometry.exists_isImmersion_projectiveSpace_comp_of_affine` with proof `sorry`.
No definitions, extra nodes, dependency repairs, or statement corrections are needed.
The copied node changes only its `lean` field.

Hypotheses and conclusion, in the order of the node:

- A commutative Noetherian ring is `(R : Type u) [CommRing R] [IsNoetherianRing R]`.
- The affine base `S = Spec R` is substituted throughout as `Spec (.of R)`; no extra
  isomorphism or choice of base is imposed.
- The two schemes are `{X Y : Scheme.{u}}`, and the two specified arrows are
  `(f : X ⟶ Y) (g : Y ⟶ Spec (.of R))`.
- Both arrows are of finite type: `[LocallyOfFiniteType f] [QuasiCompact f]` and
  `[LocallyOfFiniteType g] [QuasiCompact g]`. This is the conjunction in the recorded
  finite-type dependency, not merely local finite type.
- The hypothesis on `f` is `hf`: there exist `a : ℕ` and an arrow `i` into
  `ProjectiveSpace (ULift.{u} (Fin (a + 1))) Y`, with `IsImmersion i` and
  `i ≫ (ProjectiveSpace ... Y ↘ Y) = f`.
- The hypothesis on `g` is `hg`: there exist `b : ℕ` and an arrow `j` into the analogous
  projective space over `Spec (.of R)`, with `IsImmersion j` and its projection equal to `g`.
- Locally closed immersion has exactly the node's closed-then-open meaning:
  Mathlib's `IsImmersion.isImmersion_iff_exists` in namespace `AlgebraicGeometry.IsImmersion`
  identifies `IsImmersion` with a factorization through a closed immersion then an open
  immersion. No condition on the reverse order of these factors is imposed.
- The conclusion supplies `N : ℕ` (hence `N ≥ 0`) and an actual arrow from `X` into
  `ProjectiveSpace (ULift.{u} (Fin (N + 1))) (Spec (.of R))`, with `IsImmersion i`.
- The final equation is `i ≫ (ProjectiveSpace ... (Spec (.of R)) ↘ Spec (.of R)) = f ≫ g`.
  Lean composition is left-to-right, so this says exactly that the projection is `g ∘ f`.

Dependency signatures and docstrings were read in the pinned source:

- `def-weil-pbc-noetherian-ring`: `IsNoetherianRing`,
  `Mathlib.RingTheory.Noetherian.Defs`; all ideals are finitely generated.
- `def-weil-affine-spectrum` and `def-pc-scheme`: `AlgebraicGeometry.Spec`, `Spec.map`,
  `Scheme`, `Scheme.Hom`, in `Mathlib.AlgebraicGeometry.Scheme`.
- `def-weil-finite-type-morphism`: `AlgebraicGeometry.LocallyOfFiniteType` in
  `Mathlib.AlgebraicGeometry.Morphisms.FiniteType`, and `AlgebraicGeometry.QuasiCompact`
  in `Mathlib.AlgebraicGeometry.Morphisms.QuasiCompact`, which FiniteType imports.
- `def-weil-closed-immersion`: `AlgebraicGeometry.IsClosedImmersion`,
  `Mathlib.AlgebraicGeometry.Morphisms.ClosedImmersion`; its immersion clause is supplied
  by `AlgebraicGeometry.IsImmersion` and `IsImmersion.isImmersion_iff_exists` in
  `Mathlib.AlgebraicGeometry.Morphisms.Immersion`.
- `def-weil-open-immersion`: `AlgebraicGeometry.IsOpenImmersion`,
  `Mathlib.AlgebraicGeometry.OpenImmersion`.
- `def-nagata-projective-space-base-change`: `AlgebraicGeometry.ProjectiveSpace` and
  its `ProjectiveSpace.over` instance in
  `WeilConjectures.AlgebraicGeometry.ProjectiveSpace`. Its homogeneous coordinates are
  indexed by the supplied type, so dimension `n` requires `n+1` coordinates.

The statement reuses all these notions; it does not use the field-only
`AlgebraicGeometry.IsQuasiProjective` for the ring base or introduce a competing definition.

The four proof steps in the declaration docstring reproduce the node's direct proof:
choose the two immersions, form the pullback immersion into the product, compose,
and apply relative Segre. The proof interfaces already exist:
`ProjectiveSpace.isPullback_map` in `WeilConjectures.AlgebraicGeometry.ProjectiveSpace`;
`CategoryTheory.Limits.pullback`, its projections and universal property in
`Mathlib.CategoryTheory.Limits.Shapes.Pullback.HasPullback`;
`IsImmersion.isStableUnderBaseChange` and `IsImmersion.comp` in
`Mathlib.AlgebraicGeometry.Morphisms.Immersion` (the used clauses of the two permanence
nodes); and `ProjectiveSpace.isClosedImmersion_segre` in
`WeilConjectures.AlgebraicGeometry.ProjectiveSpace.Segre`, publicly imported by the
recorded `WeilConjectures.AlgebraicGeometry.ProjectiveSpace.Product` module of lem-chow-segre.
The latter module also supplies the recorded `ProjectiveSpace.exists_isClosedImmersion_pi`.
Proof-only modules are imported without `public`.

Source read: `literature/stacks-project/morphisms.tex`,
`lemma-composition-quasi-projective` (0C4M) and
`lemma-finite-type-over-affine-ample-very-ample` (01VT). The first composes quasi-projective
morphisms over a quasi-compact base; the second gives finite projective-space immersions
over an affine base. The node's stronger explicit embedding hypotheses and retained
Noetherian/finite-type hypotheses are stated verbatim in mathematical content.

Edge cases checked before writing: `a=0`, `b=0`, and `N=0` give one coordinate, hence the
dimension-zero projective space; Segre has dimension `ab+a+b`, including when both are zero.
Empty `X` and empty `Y` are allowed without a nonemptiness assumption. The zero ring `R`
is allowed; its spectrum is empty and arrows into it force the expected empty schemes.
There is no field, reducedness, connectedness, positive-characteristic, or nontrivial-ring
assumption. `ULift.{u}` moves the finite coordinate type into the scheme universe without
altering its cardinality, and the single arbitrary universe `u` does not restrict dimensions.
Finite type and Noetherianity are genuine hypotheses, retained even though the direct Segre
argument can establish a more general result. No statement dispute or source fault was found.

Actual searches (2026-10-19), using the prescribed `msearch.py Q05` wrapper:

- LeanFinder: `Composition of morphisms each admitting an immersion into finite dimensional
  projective space over their target admits such an immersion over an affine base`.
  Eight hits on immersion/preimmersion composition and permanence; no projective-space
  composition theorem.
- Loogle: `"QuasiProjective", "comp"`. Zero hits.
- Mathlib grep, subdirectory AlgebraicGeometry:
  `[Qq]uasi[Pp]rojective|[Qq]uasi[Pp]rojective.*comp|[Hh]as[Aa]mple`. Zero hits.
- LeanSearch: `Composition of quasi projective scheme morphisms admits immersion into
  finite projective space over affine base`. Eight hits on immersion/preimmersion
  composition, immersion construction, and cancellation; no exact statement.
- Direct `rg` of `/home/ubuntu/weil-src-slopmaster2/WeilConjectures`, `lean/Sheaf`, and
  `dag/lean_names_upstream.json` for quasi-projectivity, the item id,
  `exists_isImmersion`, and immersion composition found field-only quasi-projectivity,
  affine-source embeddings, and downstream uses, but no exact theorem. The item-id search
  found no upstream declaration. The chosen theorem name was also searched and was absent.
- Further source search for projective spaces indexed by `Fin` found existing
  `ULift.{u} (Fin 2)` conventions and `DimOneQuasiProjective`'s
  `ULift.{u} (Fin (N+1))`, confirming the dimension/universe encoding.

Validation: prescribed `scompile.py` compiled this file cleanly as both sandbox and library
module (3.0 s and 2.9 s), with no errors or warnings. All universes and variables are explicit;
there are no local definitions, instances, notation, `let` binders, or extra theorem proofs.

## Second reading by Q05

Reopened the original node and the complete module for a second clause-by-clause pass.
The ring has both commutativity and Noetherianity; the base is literally its spectrum;
both maps have both finite-type components. Each embedding hypothesis supplies a natural
dimension, an immersion into projective space over its own target, and the over-target
equation. The output likewise supplies a natural dimension and immersion, and its equation
is the composite `f ≫ g`. The `+1` in all three coordinate types was checked explicitly
against the projective-space dependency docstring. The closed-then-open interpretation was
checked against the full `IsImmersion.isImmersion_iff_exists` signature, rather than inferred
from the name alone. This pass found no omitted hypothesis, extra conclusion, or mismatch;
no change was needed. This is the worker's second pass; the maintainer performs the separate
independent delivery review, as specified in the dispatcher brief.
