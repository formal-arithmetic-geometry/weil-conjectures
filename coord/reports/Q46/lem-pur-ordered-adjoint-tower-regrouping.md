## Worker report

The module `Sheaf.CategoryTheory.OrderedAdjointTowerRegrouping` states
`CategoryTheory.orderedAdjointTower_regrouping`, with its whole proof `sorry`.
Its helpers package this node's given data and implement this node's specified
conjugate comparisons, recursive Gamma and ordered tree evaluation. None chooses
an arbitrary map, presupposes regrouping, or introduces an independent mathematical
notion needing another DAG node. The node copy changes only `lean`.

Source read: the entire current
`literature/blueprint/latest/blueprint/sec-smooth-purity/sk-prop-sp-composition/prop-pur-affine-space-composition-law.proof.md`,
especially Step 2. The item's four detailed proof steps are reproduced as a
natural-language proof in the theorem docstring. The assertion deliberately concerns
the ordered reassociation in Step 2, as the accepted node does; it does not import
the permutation assertion in the blueprint's Step 4.

Hypothesis-by-hypothesis correspondence:

- `r : ℕ` renders `r ≥ 0`; `C : Fin (r + 1) → Type u` and
  `[∀ i : Fin (r + 1), Category.{v} (C i)]` are exactly the finite family of categories.
  Object and morphism universes `u,v` are explicitly declared and independent.
- `T : OrderedAdjointTowerData r C` bundles only the given hypotheses.
  `P`, `G`, and `F` have binders `(i j : Fin (r + 1)) (h : i ≤ j)`, so the
  data exist only on ordered intervals. In particular there is no requirement to
  produce a functor between categories in the reverse direction.
- `T.P i j h : C j ⥤ C i` and `T.adj i j h : T.P i j h ⊣ T.G i j h`
  render the left functor and its given right adjunction.
  `T.F i j h : C i ⥤ C j` is the other functor.
- `P_id`, `G_id`, `F_id` identify all diagonal functors with the identity;
  `adj_id` identifies the diagonal adjunction with Mathlib's `Adjunction.id`
  after these type identifications (`HEq` is equality across those types).
  Thus an arbitrary automorphism of a diagonal adjunction is not admitted.
- `alpha i j k hij hjk` has type `P_jk ⋙ P_ij ≅ P_ik` and
  `phi i j k hij hjk` has type `F_ik ≅ F_ij ⋙ F_jk`.
  Lean's `⋙` writes application in the reverse textual order to the node's
  conventional right-to-left notation for functor composition.
- `alpha_assoc` is the left-comparison pentagon on each object of `C_l`:
  alpha_ijk at P_kl(X), then alpha_ikl, equals P_ij(alpha_jkl), then alpha_ijl.
  `phi_assoc` is the F pentagon on each object of `C_i`, in the corresponding
  opposite orientation. Both quantify over all `i ≤ j ≤ k ≤ l`.
- `alpha_left_unit` and `alpha_right_unit` are exactly the two unit equations,
  with `eqToIso` for diagonal equality and the standard functor unitors.
  `phi_left_unit` and `phi_right_unit` are the analogous inverse-oriented
  equations. They include all `i ≤ k`, also `i=k`.
- `eta : ∀ j : Fin r, F_(j,j+1) ⟶ G_(j,j+1)` is the arbitrary adjacent
  natural transformation. There is no `IsIso` or invertibility hypothesis.

Construction and clause-by-clause correspondence:

- `T.comparison i j k hij hjk` is precisely `c_ijk`, defined by
  `conjugateIsoEquiv (T.adj i k ...) ((T.adj j k ...).comp (T.adj i j ...))`
  applied to `T.alpha i j k ...`. Mathlib's `comp_counit_app` gives
  `P_ij.map (epsilon_jk.app (G_ij.obj K)) ≫ epsilon_ij.app K`, namely the
  counit stipulated by the node. There is no new choice of right comparison.
- `T.diagonal i` is the identity `Gamma_ii`, with only the given identity-functor
  equality transports. `T.join i j k hij hjk a b` is the natural transformation
  `phi.hom ≫ whiskerRight a F_jk ≫ whiskerLeft G_ij b ≫ c.inv`.
- `T.gamma eta j i h` is `Gamma_ij` (the final endpoint is first because the
  recursion uses `Fin.induction` on it). At equal endpoints its branch is
  `T.diagonal`. At `j+1` with `i<j+1`, it is the actual join of the recursively
  constructed `Gamma_ij` and `eta_j`, so on each object its four factors are
  exactly the node's defining recurrence. It is not an arbitrary family
  satisfying a desired block law. All helper definitions contain full data.
- The theorem's first conjunct is the c pentagon on components:
  `c_ikl.hom.app X ≫ G_kl.map (c_ijk.hom.app X)` equals
  `c_ijl.hom.app X ≫ c_jkl.hom.app (G_ij.obj X)`.
- The second and third conjuncts are the two c unit equations. They are the
  inverse-oriented right-adjoint unitors, with diagonal equality transports.
- The fourth conjunct explicitly states naturality for every `Gamma_ij`, every
  `X,Y : C i` and every `f : X ⟶ Y`. Its natural-transformation type already
  carries the same property, since the recursion composes natural transformations.
- The fifth conjunct is precisely the displayed block identity for all ordered
  `i,j,k` and `X : C i`, in Lean's left-to-right morphism composition order:
  `phi_ijk`, `F_jk(Gamma_ij)`, `Gamma_jk` at `G_ij(X)`, then `c_ijk.inv`.
- The sixth conjunct states the actual parenthesization conclusion.
  `OrderedAdjointTowerTree` has adjacent leaves, empty intervals and joins of two
  consecutive intervals. Its recursive `eval` uses `eta`, `diagonal` and the
  specified `join`. Every such tree evaluates to `T.gamma eta j i h`; therefore
  any two trees of the same interval have equal transformations. Joining can
  insert empty intervals but cannot permute any leaves.

Dependency declarations read and used:

- `def-weil-pbc-composite-adjunction` is a Mathlib leaf, with no `lean` record
  required. Its match is `CategoryTheory.Adjunction.comp` in
  `Mathlib.CategoryTheory.Adjunction.Basic`, including `comp_counit_app`,
  `comp_homEquiv` and `Adjunction.id`. These are imported through Mates.
- `def-weil-pbc-adjunction-conjugate` is a Mathlib leaf. Its matched
  `CategoryTheory.conjugateEquiv` and `conjugateIsoEquiv` in
  `Mathlib.CategoryTheory.Adjunction.Mates` give exactly the specified conjugate.
  Their signatures and docstrings were read; `comparison` uses `conjugateIsoEquiv`.
- The stated proof dependency `lem-weil-pbc-mate-pasting` is the same Mathlib
  module's `mateEquiv_vcomp`, `mateEquiv_hcomp`,
  `mateEquiv_conjugateEquiv_vcomp`, `conjugateEquiv_mateEquiv_vcomp` and
  `conjugateEquiv_id`. Its module is already a public statement import, so no
  duplicate plain import is needed. The docstring names the precise clauses.
- `Mathlib.Order.Fin.Basic` supplies the finite linear order used for interval
  inequalities. Standard natural transformations, isomorphisms, whiskering,
  equality transports and unitors are Mathlib's, not copies.

Edge cases checked before and during writing:

- `r=0`: `Fin r` is empty, no `eta` is requested, and the only interval is the
  identity at level zero. Empty-tree joins still evaluate by the unit equations.
- `i=j`, `j=k`, and `i=j=k`: gamma is the transported identity and the block
  formula reduces using the two F and c units. No strict inequality was silently
  introduced in that formula or the coherence equations.
- A one-edge interval uses the successor branch with the diagonal previous value;
  its two unit comparisons reduce the result to precisely the given `eta`.
- Empty categories are allowed. Only ordered functors supplied by the statement
  are requested; no nonexistent reverse functor is imposed.
- Zero or other noninvertible adjacent transformations are allowed (when the
  categories have them); only the given comparison isomorphisms are inverted.
- The initial and final indices can be any ordered indices, not only zero and r.
  All quantified types and universe names are bound; autoImplicit is disabled.

Searches made (2026-10-24):

- `msearch.py leanfinder`: "Natural transformations to right adjoints along a
  finite ordered tower are independent of parenthesization using coherent
  adjunction conjugates". Eight hits, including
  `Adjunction.leftAdjointCompNatTrans_assoc`, the two
  `leftAdjointCompNatTrans...eq_conjugateEquiv_symm` lemmas and
  `Adjunction.rightAdjointUniq_trans`. These are finite comparison building
  blocks, not the full arbitrary-eta recurrence and all-tree assertion.
- `msearch.py loogle`: `CategoryTheory.conjugateEquiv, CategoryTheory.Adjunction.comp`.
  Twelve hits, including the conjugate unitor, whiskering and associator lemmas
  and `iterated_mateEquiv_conjugateEquiv`. They provide the mate-coherence inputs,
  not this ordered-tower statement.
- `msearch.py grep`, subdirectory `CategoryTheory`:
  `ordered.*(adjoint|tower)|regroup|conjugateIsoEquiv`. Twenty-four hits concern
  standard conjugate constructions, CompositionIso, Unique, Opposites and related
  applications. None is the complete statement.
- `rg` on both `lean/WeilConjectures` and `lean/Sheaf` for
  `ordered.*(adjoint|tower)|regroup|lem-pur-ordered-adjoint-tower-regrouping`:
  no existing attachment for this node. Related finite scalar tower mates and
  affine-trace recursions were opened; they state geometric/scalar comparisons,
  not the generic arbitrary-eta block law. The required literal node-id search
  likewise finds no upstream declaration.
- `rg` on Mathlib, both library roots and `dag/lean_names_upstream.json` for
  `orderedAdjointTower|OrderedAdjointTower`: no declaration-name collisions.

There are no disputed statements, statement changes, new nodes or dependency repairs.
Compilation uses only the prescribed `scompile.py`; final delivery preflight and
per-file validation are recorded below.

## Second reading by Q46

A second pass in this same worker session compared the completed source against the
node, with the source proof open. The dispatcher expressly prohibits starting other
agents, so this is a worker self-check, not a claim of an independent agent review;
the maintainer supplies the independent delivery review.

Checked every hypothesis and conjunct against the mapping above. In particular the
P composition order, the order of `Adjunction.comp`, the orientation of the
conjugate and both c unitors agree with the node. The F and c pentagons use all
weakly ordered quadruples, the block formula includes repeated endpoints, and the
tree leaf is exactly the corresponding adjacent `eta`. The recursion constructs
Gamma without a block-law hypothesis. The only implementation fixes found were
the required `Order.Fin.Basic` import and explicit conversion of finite-index
strict inequalities to natural-number inequalities in the predecessor branch.
No mathematical hypothesis or conclusion changed.
