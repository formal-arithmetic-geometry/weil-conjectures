## Worker report

The module `Sheaf.AlgebraicGeometry.GroupScheme.StrictDominantFlagLineAmple` states
`AlgebraicGeometry.strictDominant_flagLine_ample`. Its only theorem proof is `sorry`;
there are no definitions or chosen objects. The node statement, proof, and proof
dependencies are unchanged. Two already-landed definition nodes are added to
`stmt_deps`, identifying the owners of semisimplicity and the associated-bundle
presentation used in the signature.

Source read: Milne, Algebraic Groups (2017), printed pp.479–480, Theorem 22.48
and Remark 22.49 (PDF pages 491–492). The displayed action is
`(g,x)b=(gb,χ(b)⁻¹x)`. Remark 22.49 identifies its divisor coefficients with
`⟨w₀χ,α∨⟩`. For χ=-mu this permutes the positive simple-coroot coefficients of
mu. This checks the sign, rather than relying on the potentially confusing use
of dominant in the following printed vanishing theorem. The geometric inputs
are Milne 17.9, 21.73 and Remark 21.74. The absolute ampleness definition was
read in the recorded upstream module, matching Stacks Tag 01PS. The node's
Jantzen source is WANTED; no claim is made to have read that unavailable source.

Hypothesis and conclusion correspondence:

- The arbitrary algebraically closed field is `{F : Type u} [Field F]
  [IsAlgClosed F]`, with an explicit universe and `autoImplicit false`.
- `G : Grp (Over (Spec (.of F)))` is the group scheme called S in the node.
  `hG : IsSemisimpleGroupScheme G.X` means smooth, connected, affine, finite
  type, with no nontrivial smooth connected solvable normal closed subgroup.
  I read its definition and its derived-length/solvability definitions in
  `Sheaf.AlgebraicGeometry.GroupScheme.Semisimple`.
- `hsc` is exactly simple connectedness as written in the node: every
  semisimple group scheme G' with a surjective group homomorphism to G and
  finite central scheme-theoretic kernel maps isomorphically. The kernel is
  `GrpObj.ker f`, finiteness is `IsFinite (GrpObj.ker f).hom`, centrality is
  equality of products for all commutative F-algebras, and the conclusion is
  `IsIso f`. Test-algebra universes match F, without a smaller independent
  universe. This is the same interface as the character-lattice dependency.
- `T B`, `iT iB`, `j`, `hj` specify T⊆B⊆G. `hT` is the recorded maximal-torus
  predicate; `hsplit` gives an isomorphism to a product of multiplicative
  groups, permitting r=0. `hB` is the recorded Borel predicate, whose full
  definition was read (closed, smooth, connected, solvable and maximal).
- The actual character lattice is
  `Additive (T ⟶ Grp.mk (StandardGroupSchemes.multiplicative F))`, and the
  cocharacter lattice is the reverse Hom group. The commutativity instance
  binders express their canonical commutative structures, as in the recorded
  Borel-pair and character-lattice declarations. No artificial lattice is used.
- `aG aB` and `haG haB` pin the actions to conjugation by the given inclusions.
  `Φ P b` are the finite roots, integral root datum and simple base.
  `hroot` identifies roots with actual characters, `hpair` identifies the
  integer pairing with composition/power maps on G_m, `hweights` says that
  these are precisely the nonzero character weights in Lie(G), and
  `hpositive` says that positives are precisely the weights in Lie(B).
  These are the exact recorded Borel-pair signature, not extra root-data
  assumptions or a differential-character replacement in characteristic p.
- `U iU hU` specify the unipotent radical: a smooth connected normal unipotent
  closed subgroup containing every such subgroup. `p`, `hp`, `hker` specify
  the projection B→T, identity on T, with that scheme-theoretic kernel.
  These are the data already fixed by the node's reference to the Borel-pair
  theorem, not a choice of an arbitrary retraction.
- `Q π hπflat hπsurj hπinv hπtorsor` specify Q=G/B by its faithfully flat
  right B-torsor kernel pair, exactly as in the recorded dependency. Properness,
  smoothness or projectivity of Q are not added as assumptions.
- The first three conclusions are `Smooth Q.hom`, `IsProjective Q.hom`
  (the blueprint's H-projective plus quasi-compact convention), and
  `GeometricallyIntegral Q.hom`. The last is the Mathlib predicate asserting
  integrality after field base change; its definition and integral predicate
  were read. All three hold independently of the weight.
- The quantifier `∀ mu` ranges over all actual torus characters, and
  `∀ α : b.support, 0 < P.toLinearMap mu (P.coroot α)` is strict positivity
  on every simple coroot, with integer values.
- `M : AssociatedCharacterLineBundle.Presentation G B iB Q π
  (p ≫ (-mu).toMul)` is precisely the presentation of L_(-mu∘p).
  The existing presentation records the actual quotient action, pullback
  trivialization, natural representing section sheaf and geometric left
  action. Because its action scalar is the inverse of the character, the
  scalar here is mu(p(b)), as required. Its full structure was read. The
  quantifier permits every presentation; existence is already supplied by
  `exists_homogeneousLineBundle_sections` and is not a new assumption.
- `∃ hM : M.L.IsInvertible, @Scheme.Modules.IsAmple Q.left M.L hM`
  asserts invertibility and the recorded absolute ampleness predicate of the
  same sheaf. The explicit hM passes the invertibility instance required by
  that predicate without adding an instance hypothesis or a hidden let.

Dependency declarations read and used:

- `Mathlib.Algebra.Field.Defs`: `Field`; `Mathlib.FieldTheory.IsAlgClosed.Basic`:
  `IsAlgClosed` (the algebraic-closure node's match explicitly names it).
- `Mathlib.CategoryTheory.Monoidal.Grp`: `CategoryTheory.GrpObj`, `Grp`;
  `WeilConjectures.AlgebraicGeometry.GroupScheme.Defs`: the group-scheme,
  closed/normal subgroup and finite-kernel interfaces documented there.
- `Sheaf.AlgebraicGeometry.GroupScheme.ReductiveBorelPairStructure`:
  `reductive_borel_pair_structure`, `semisimpleGroupScheme_isReductive`;
  the former's full signature and proof docstring were read. All root datum,
  radical, projection and torsor hypotheses use that signature.
- `Sheaf.AlgebraicGeometry.GroupScheme.HomogeneousLineBundleSections`:
  `exists_homogeneousLineBundle_sections`, full statement and proof read;
  `Sheaf.AlgebraicGeometry.GroupScheme.AssociatedCharacterLineBundle`:
  `AssociatedCharacterLineBundle.Presentation`, with every field read.
- `Mathlib.AlgebraicGeometry.Morphisms.Smooth`: `Smooth`;
  `WeilConjectures.AlgebraicGeometry.Morphisms.Projective`: `IsProjective`;
  `Mathlib.AlgebraicGeometry.Properties`: `IsIntegral`;
  `Mathlib.AlgebraicGeometry.Geometrically.Integral`: `GeometricallyIntegral`;
  `WeilConjectures.AlgebraicGeometry.Ample`: `Scheme.Modules.IsAmple`.
- Proof imports: `Sheaf.AlgebraicGeometry.GroupScheme.BruhatLongestCellCharts`
  (`bruhat_longest_cell_charts`), `SimplyConnectedCharacterLattice`
  (`simplyConnected_character_lattice`), `BorelCharacteristicPicardSequence`
  (`borel_characteristic_picard_sequence`), and
  `Sheaf.Algebra.Category.ModuleCat.Sheaf.CochainTensorUniverses`
  (`SheafOfModules.cochainModulesMonoidal`). Their declarations/docstrings
  were read; these imports are non-public as required.
- `lem-sfb-flag-torus-fixed-geometry` and
  `lem-sfb-fundamental-flag-boundary-sections` currently have no Lean record;
  there is no module to import for these proof-only dependencies. They remain
  named in the proof docstring and unchanged in proof_deps. Neither is needed
  to type the statement; no prerequisite statement is fabricated for them.

Edge cases checked before writing: for the trivial group the torus and actual
character lattice have rank zero, b.support is empty and the strict inequalities
are vacuous. The quotient is Spec F, the character is zero and the associated
module is O, ample by its section 1. No positive-rank binder excludes this case.
For SL₂ with the positive root in Lie(B), a positive fundamental weight gives
M_ω=O(1) on P¹; weight zero fails strict dominance when rank is positive.
For products, every simple-factor coefficient must be positive, giving O(a,b)
on P¹×P¹ with a,b>0. In positive characteristic all weights are actual characters
and all pairings are integers, so no differential or characteristic-zero
assumption is introduced. Empty Q is excluded by being the surjective quotient
of a group scheme with an identity, not by an added Nonempty hypothesis.

Searches actually run:

- `msearch.py leanfinder`: "Strictly dominant characters give ample homogeneous
  line bundles on flag schemes" → eight generic Proj and affine-cover results;
  no matching flag-line theorem.
- `msearch.py loogle`: "IsAmple, RootDatum" → zero hits, unknown identifier
  IsAmple in the search index. This does not deny the upstream project predicate.
- `msearch.py grep`: "strict.*dominant|dominant.*ample|flag.*ample" → eight
  unrelated Gershgorin and birational-dominance hits in Mathlib.
- `rg -n` with that pattern and the item id in `lean/WeilConjectures` and
  `lean/Sheaf` → unrelated dominant-morphism comments and affine-reflection
  descent, no duplicate declaration or theorem.
- Declaration-directed source searches found the already-landed presentation,
  semisimplicity, root-pairing, projectivity and ampleness interfaces listed
  above. No new definition or dependency repair is necessary.

No statement correction or STATEMENT-DISPUTED fault. Initial compilation found
that the identifier μ clashes with the opened monoid-object notation; its Lean
binder was renamed mu without changing any mathematical content.

Validation: the final module compiled cleanly through scompile.py in both its
sandbox and library-name checks (2.6 s and 2.4 s). deliver2.py --no-push then
reported OK: preflight passed and the file compiled. No additional proof beyond
the prescribed sorry was supplied. The maintainer performs the independent
reading under the dispatcher workflow; no worker second reading is claimed.

## Second reading by NG

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
