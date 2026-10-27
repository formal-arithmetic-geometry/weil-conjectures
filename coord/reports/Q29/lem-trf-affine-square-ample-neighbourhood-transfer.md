## Worker report

The module `Sheaf.AlgebraicGeometry.AffineSquareAmpleNeighbourhoodTransfer` states
`AlgebraicGeometry.Scheme.Modules.affine_square_ample_neighbourhood_transfer`.
Its only new declaration is this theorem, with proof `sorry`, as required for stage 2.
No new definition, dependency repair, or statement correction is needed. The node copy
changes only `lean`, whose signature is copied verbatim from the module.

Source read: `literature/stacks-project/more-morphisms.tex`,
`lemma-ample-in-neighbourhood` (Tag 0D2S), especially its final paragraph and hints.
Those hints use affine pullback of ampleness; the node expands that transfer into an
arbitrary commutative square. The supplied four proof steps are reproduced in the
Lean docstring, including the inverse-image identity, restricted affine map, pullback
and restriction comparisons, quasi-compactness, and second affine pullback for W.

Hypothesis-by-hypothesis and clause-by-clause correspondence:

- The four schemes are `{X Y Z S : Scheme.{u}}`; the morphisms are
  `(f : Y ⟶ X) (g : Z ⟶ S) (a : Y ⟶ Z) (b : X ⟶ S)`.
  The universe is explicit and arbitrary; auto-implicit binding is disabled.
- The equation g composed with a = b composed with f is
  `hsquare : a ≫ g = f ≫ b`, using Lean's left-to-right category composition.
  There is no Cartesian-square assumption.
- Affineness of a and b is `[IsAffineHom a] [IsAffineHom b]`.
  No affineness, properness, or quasi-compactness assumption is imposed on f or g.
- The modules are `(N : Z.Modules) (M : Y.Modules)`, with
  `[N.IsInvertible] [M.IsInvertible]`.
- The given pullback isomorphism is `e : (tensorPullback a).obj N ≅ M`.
  This is the tensor-formula pullback of the dependency, not an unspecified functor.
- The affine base open is `(V : S.Opens) (hV : IsAffineOpen V)`.
- The hypothesis on N restricted to g inverse V is `hN : @IsAmple
  (g ⁻¹ᵁ V).toScheme ((tensorPullback (g ⁻¹ᵁ V).ι).obj N) ...`.
  The last argument is the invertibility proof
  `((invertible_pullback_tensor (g ⁻¹ᵁ V).ι).1 N).2`, already supplied by the
  recorded dependency, so it introduces no hypothesis.
- U is written directly as `b ⁻¹ᵁ V`. Its being an affine open is the first
  conjunct `IsAffineOpen (b ⁻¹ᵁ V)`; the Opens type supplies openness.
- Quasi-compactness of f inverse U is the second conjunct
  `CompactSpace (f ⁻¹ᵁ (b ⁻¹ᵁ V)).toScheme`.
- Absolute ampleness of M restricted to f inverse U is the third conjunct,
  with scheme `(f ⁻¹ᵁ (b ⁻¹ᵁ V)).toScheme` and module
  `((tensorPullback (f ⁻¹ᵁ (b ⁻¹ᵁ V)).ι).obj M)`.
- The final clause is `∀ (W : X.Opens), W ≤ b ⁻¹ᵁ V → IsAffineOpen W → ...`.
  Opens of U are equivalently opens of X contained in U. The resulting module
  is the restriction `((tensorPullback (f ⁻¹ᵁ W).ι).obj M)` on `(f ⁻¹ᵁ W).toScheme`.
  Each ampleness conclusion uses its dependency-supplied invertibility witness.

Dependency declarations read and used:

- `Mathlib.AlgebraicGeometry.Scheme`: `AlgebraicGeometry.Scheme` and `Scheme.Hom`.
- `Mathlib.AlgebraicGeometry.Morphisms.Affine`: `AlgebraicGeometry.IsAffineHom`;
  also its affine-preimage, affine-schemes, and base-change declarations for the proof plan.
- `WeilConjectures.AlgebraicGeometry.Modules.Invertible`:
  `AlgebraicGeometry.Scheme.Modules.IsInvertible`.
- `Sheaf.AlgebraicGeometry.TensorPullbackSectionAdjunction`: public interface of
  `def-pc-module-pullback`, retaining `tensorPullback` from
  `WeilConjectures.AlgebraicGeometry.TensorPullback`. Read the tensor object/functor
  construction and the normalized adjunction and composition signatures.
- `WeilConjectures.AlgebraicGeometry.Ample`:
  `AlgebraicGeometry.Scheme.Modules.IsAmple`, the absolute predicate including
  compactness and affine nonvanishing neighbourhoods of positive tensor powers.
- `Mathlib.Topology.Defs.Filter`: `CompactSpace`, with no separation assumption.
- `WeilConjectures.AlgebraicGeometry.Modules.InvertiblePullbackTensor`:
  `AlgebraicGeometry.Scheme.Modules.invertible_pullback_tensor`; its first conjunct
  supplies the explicit restriction invertibility proofs used in the signature.
- Proof-only imports include `WeilConjectures.AlgebraicGeometry.AmpleIso`
  (`isAmple_iff_of_iso`), `Sheaf.AlgebraicGeometry.TensorPullbackOpenRestriction`
  (`restrictFunctorIsoTensorPullback` and its unit theorem), and
  `WeilConjectures.AlgebraicGeometry.AmplePullback`
  (`isAmple_tensorPullback_of_isAffineHom`). Mathlib pullbacks, open immersions,
  separated morphisms and limits supply the remaining recorded proof dependencies.

Edge cases checked before writing:

- V empty gives U and its inverse image empty. The empty scheme is quasi-compact;
  the pointwise ampleness condition is vacuous. No nonempty binder excludes it.
- W empty is permitted; W = U is also permitted since the conclusion proves U affine.
- V = top is permitted when S is affine; the conclusion then transfers global
  ampleness and gives quasi-compactness without requiring X or S quasi-compact
  independently of their applicable affine opens.
- Non-Cartesian squares are included: commutativity alone gives
  f inverse (b inverse V) = a inverse (g inverse V); the restriction of a is affine.
- The final assertion does not claim preservation under arbitrary open restriction.
  W and U are both affine, so W → U is affine; its inverse image inclusion is affine.
  Thus the affine pullback argument applies, including on non-Noetherian schemes.
- All module invertibility witnesses are derived, not extra restriction hypotheses.

Searches actually run using msearch.py with group Q29 and this item:

1. leanfinder: "In an affine commutative square of schemes transfer an ample line
   bundle on the inverse image of an affine open to its pullback and all affine subopens".
   Result: OK, 8 hits, including `of_targetAffineLocally_of_isPullback`,
   `HasAffineProperty.of_isPullback`, and affine-target local properties; no match
   for the combined ampleness statement.
2. loogle: `"IsAmple", "IsAffineHom"`. Result: OK, 0 hits.
3. grep: `ample.*(square|neighbou)|affine.*ample` in Mathlib AlgebraicGeometry.
   Result: OK, 0 hits.
4. leansearch: "Absolute ampleness of an invertible sheaf transfers through a
   commutative square with affine horizontal maps over every affine subopen".
   Result: OK, 8 hits, including affine base-change stability and affine-local
   morphism properties. None states the ampleness transfer theorem.
5. rg in both `lean/WeilConjectures` and `lean/Sheaf`:
   `ample.*(square|neighbou)|affine.*ample|lem-trf-affine-square-ample-neighbourhood-transfer`
   (case insensitive). Results include the generic affine ample pullback theorem,
   the parent AmpleNeighbourhood module, and SchemeRelativeAmpleAffineCover. Read
   these interfaces; none states this node's four conclusions with these hypotheses.
6. rg for the exact node id and `affine_square_ample_neighbourhood_transfer` in
   `dag/lean_names_upstream.json`, `lean/WeilConjectures`, and `lean/Sheaf`: no hits.

Validation: scompile.py compiled both the sandbox probe and the actual library module
on the server cleanly (1.8 s and 1.7 s respectively). No diagnostics were emitted.
The file uses module mode, public statement imports, proof-only plain imports, explicit
universes, and no line longer than 100 characters. No STATEMENT-DISPUTED finding.

## Second reading by Q29

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
