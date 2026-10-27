## Worker report

The module `Sheaf.AlgebraicGeometry.PolarizedFormalAlgebraization` states
`AlgebraicGeometry.polarized_formal_algebraization`, with its entire proof `sorry`.
It introduces no definition and changes only the item's `lean` field.
The source read was `literature/stacks-project/coherent.tex`, theorem-algebraization
(Tag 089A), its entire proof, and the closed-subscheme construction at Tag 0899.
The declaration's docstring carries all ten DAG proof steps and their dependencies.
The empty legacy CompactObject example was checked against its node's current
upstream attachment; the delivered file uses the current module-system header.

Clause-by-clause correspondence:

- A commutative Noetherian ring: `(A : Type u) [CommRing A] [IsNoetherianRing A]`.
- An ideal and separated adic completeness: `(I : Ideal A) [IsAdicComplete I A]`.
  This is the recorded Mathlib predicate, including its Hausdorff condition.
- S and the positive quotient bases: `Spec (.of A)` and
  `Spec (.of (A ⧸ I ^ (n + 1)))`. The change of index is a bijection between Lean
  naturals and the paper's positive integers, so all levels are present.
- The schemes and their structural maps: `X : ℕ → Scheme.{u}` and `f n` into the
  indicated quotient spectrum. Universes are explicit and shared as in the
  recorded scheme and module interfaces.
- The transitions are `i n : X n ⟶ X (n + 1)`. The bottom arrow is the actual
  `Spec.map` of `Ideal.Quotient.factor (Ideal.pow_le_pow_right ...)`.
  `hcart` is `IsPullback (i n) (f n) (f (n + 1))` of that bottom arrow, which
  supplies both commutativity over the quotient base and the cartesian property.
- Properness is assumed only at the first stage: `[IsProper (f 0)]`.
  No flatness, finite presentation, or properness of all levels is assumed.
- The actual line bundles are `L n : (X n).Modules` with
  `[∀ n : ℕ, (L n).IsInvertible]`. The specified transition identifications are
  `φ n : (Scheme.Modules.tensorPullback (i n)).obj (L (n + 1)) ≅ L n`.
- The special-fibre ampleness hypothesis is
  `hample : Scheme.Modules.IsAmple (X 0) (L 0)`, the recorded absolute notion.
- The algebraization is an existential `Y : Scheme.{u}` and
  `g : Y ⟶ Spec (.of A)` with `IsProper g`.
- Its finite-projective-space projectivity is `IsHProjective g`, exactly the
  recorded convention. It gives a closed immersion over S into projective space
  with finitely many homogeneous coordinates. A nonempty finite coordinate set
  is identifiable with `Fin (N+1)`; an empty one forces empty Y, which embeds
  into projective zero-space. Thus this is the node's N ≥ 0 convention.
- The algebraized line is `M : Y.Modules`, its invertibility witness is `hM`,
  and its ampleness is `@Scheme.Modules.IsAmple Y M hM`.
- `a n : X n ≅ pullback g (Spec.map (CommRingCat.ofHom
  (Ideal.Quotient.mk (I ^ (n + 1)))))` is the requested scheme isomorphism.
  The first universal equation says `(a n).hom ≫ pullback.snd ... = f n`;
  therefore the isomorphism is over the specified S_n, not just over S.
- `hcompat n` says `i n ≫ ((a (n+1)).hom ≫ pullback.fst ...) =
  (a n).hom ≫ pullback.fst ...`. This is exactly the Y projection of the
  required equality with the canonical base-change transition. Its other
  projection follows from the preceding over-S_n equation and `(hcart n).w`.
  The two-projection universal property of the pullback makes these conditions
  equivalent to the full scheme compatibility in the node; it loses no clause.
- `b n` is an isomorphism from tensor pullback of M along precisely
  `(a n).hom ≫ pullback.fst ...` to the prescribed `L n`.
- The last equation expresses the specified compatibility of these b's.
  Its left side first uses `(tensorPullbackSectionComp (i n) kNext).hom.app M`
  to identify pullback along the composite with iterated pullback, then uses
  `(tensorPullback (i n)).map (b (n+1)).hom`, and finally `(φ n).hom`.
  Its right side transports the source using `eqToIso (congrArg ... (hcompat n))`
  and then applies `(b n).hom`. All terms are in the same Hom set. Thus this
  recovers the given φ_n, including its scalar normalization, rather than
  asserting only that the restriction bundles are isomorphic.

Statement dependency declarations read and used:

- `def-weil-pbc-noetherian-ring`: `Mathlib.RingTheory.Noetherian.Defs`, `IsNoetherianRing`.
- `def-weil-pbc-adically-complete-ring`: `Mathlib.RingTheory.AdicCompletion.Basic`, `IsAdicComplete`.
- `def-weil-affine-spectrum`: `Mathlib.AlgebraicGeometry.Scheme`, `AlgebraicGeometry.Spec`.
- `def-pc-scheme`: `Mathlib.AlgebraicGeometry.Scheme`, `AlgebraicGeometry.Scheme`.
- `def-pc-fibre-product`: `Mathlib.CategoryTheory.Limits.Shapes.Pullback.HasPullback`, `CategoryTheory.Limits.pullback`.
- `def-weil-proper-morphism`: `Mathlib.AlgebraicGeometry.Morphisms.Proper`, `AlgebraicGeometry.IsProper`.
- `def-sc-invertible-module`: `WeilConjectures.AlgebraicGeometry.Modules.Invertible`, `AlgebraicGeometry.Scheme.Modules.IsInvertible`.
- `def-pc-module-pullback`: `Sheaf.AlgebraicGeometry.TensorPullbackSectionAdjunction`, `AlgebraicGeometry.Scheme.Modules.tensorPullbackSectionAdjunction`.
- `def-weil-pbc-ample-invertible-module`: `WeilConjectures.AlgebraicGeometry.Ample`, `AlgebraicGeometry.Scheme.Modules.IsAmple`.
- `def-kun-projective`: `WeilConjectures.AlgebraicGeometry.Morphisms.Projective`, `AlgebraicGeometry.IsHProjective`.

For module pullback, the recorded module publicly supplies the upstream explicit
`Scheme.Modules.tensorPullback` and defines the canonical
`Scheme.Modules.tensorPullbackSectionComp` using the uniquely section-normalized
adjunction. I read both constructions and use the latter in the final equation.
Statement dependencies are public imports; the already recorded proof modules
are plain imports. The two proof nodes without declarations at this base,
`lem-sfb-proper-nilpotent-base-change-reflection` and
`lem-sfb-very-ample-affine-finite-sections`, have no module to import yet; their
uses remain explicit in the proof docstring. No unstated prerequisite is needed
to type this statement.

Edge cases checked before drafting:

- I = 0: the tower consists of cartesian isomorphic stages; all prescribed line
  transition identifications remain represented, and the theorem reduces to
  algebraizing a constant polarized proper scheme.
- I = A: separated completeness forces A to be the zero ring; the bases and
  all their schemes are empty, which is allowed by every binder and conclusion.
- Empty first fibre: cartesianness across nilpotent quotient immersions forces
  every stage empty; the empty algebraization and its line bundle are allowed.
- Nonflat systems are admitted. The source only needs properness of the first
  stage and an ample first line bundle; no flatness assumption was introduced.
- Projective dimension N = 0 and every positive infinitesimal level are included.
- Arbitrary φ_n are retained in the actual compatibility equation, so changing
  their scalars is not silently discarded by a bare existence statement.

Searches actually run:

- `msearch.py ... leanfinder`: “compatible proper schemes over an adically
  complete Noetherian ring with compatible ample invertible modules algebraize”.
  Eight hits concerned affine transition limits and properness of Proj; none
  states polarized formal algebraization.
- `msearch.py ... loogle`: `IsAdicComplete, IsProper`.
  It returned zero hits with “unknown identifier 'IsProper'”; this query did
  not give a usable indexed match, and is not evidence that IsProper is absent.
- `msearch.py ... grep`: `algebraiz|Algebraiz|polarized|Polarized` restricted to
  `AlgebraicGeometry`. Twenty-five Mathlib hits were uses of the algebraize
  tactic in unrelated ring-map proofs; none was the requested theorem.
- Direct `rg` of `lean/WeilConjectures` and `lean/Sheaf` for polarized/formal
  algebraization located the existing formal-curve consumer and coherent-module
  algebraization results, but no statement of this theorem. A subsequent exact
  `grep -rn` for this node id in `lean/WeilConjectures` returned no match.
- Exact declaration-name searches for `polarized_formal_algebraization` and
  `polarizedFormalAlgebraization` in both source roots and
  `dag/lean_names_upstream.json` returned no matches.

No new node, dependency repair, statement correction, or disputed statement is
needed. The recorded dependency interfaces express every object in the source.

Validation: `scompile.py` checked the module both as a sandbox module and under
its delivered library name; both compilations passed with no errors or warnings
(2.5 s and 2.4 s respectively). The Lean file has no lines exceeding 100
characters and both automatic-implicit options are disabled explicitly.

## Second reading by N9

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
