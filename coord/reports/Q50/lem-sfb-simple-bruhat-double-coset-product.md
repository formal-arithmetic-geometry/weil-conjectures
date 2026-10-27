## Worker report

The module `Sheaf.AlgebraicGeometry.GroupScheme.SimpleBruhatDoubleCosetProduct`
states `AlgebraicGeometry.simple_bruhat_double_coset_product` with `sorry`.
Its two real helper definitions belong to the same notion: `simpleBruhatWordLength`
is the infimum of lengths of lists of specified simple reflections whose ordered
product is the given element; `simpleBruhatDoubleCoset` specializes Mathlib's
`DoubleCoset.doubleCoset` to the existing Borel point-image subgroup and the
chosen normalizer representative. Neither helper postpones any data or proof.
There is one theorem, one sorry, and no new independent mathematical notion.

Hypotheses and clauses, in the order of the node:

- The algebraically closed field F is `{F : Type u} [Field F] [IsAlgClosed F]`.
- The group scheme is `G : Grp (Over (Spec (.of F)))`. The actual group-object
  structure on the scheme, including its functor-of-points group law, is inherited
  from `Grp` and `GrpObj`, not an arbitrary abstract group.
- Semisimplicity is `hG : IsSemisimpleGroupScheme G.X`. Opening its definition gives
  smoothness, connectedness, affineness, locally finite type and quasi-compactness
  (finite type), and triviality of every smooth connected solvable normal closed
  subgroup. Its solvability is the terminating scheme-theoretic derived series.
- Simple connectedness is written out as `hsc`: for every semisimple group scheme
  G' and group-scheme homomorphism f to G, surjectivity and finite central kernel
  imply `IsIso f`. Centrality quantifies over every commutative F-algebra A,
  every A-point x of the actual kernel `GrpObj.ker f`, and every A-point g of G',
  requiring `(x ≫ GrpObj.kerι f) * g = g * (x ≫ GrpObj.kerι f)`.
- The fixed split maximal torus is `T`, its inclusion `iT`, `hT : IsMaximalTorus iT`,
  and `hsplit : ∃ r, Nonempty (T ≅ splitTorus F r)`. The fixed Borel is `B`, `iB`,
  and `hB : IsBorelGroupScheme iB.hom.hom`. The inclusion T into B is `j`, and
  `hj : j ≫ iB = iT` is exactly containment with the specified embeddings.
- The root datum supplied by reductive_borel_pair_structure is D on the actual
  additive character/cocharacter Hom lattices, with `base : D.Base` and `hred`.
  `hroot` identifies its root labels with the actual characters; `hpair` identifies
  its integral pairing with composition into the corresponding power morphism.
  `aG`, `aB`, `haG`, `haB` specify the actual conjugation actions. `hΦ` identifies
  all roots with precisely the nonzero character weights in Lie(G), and `hpos`
  identifies the positive roots with those occurring in Lie(B). The two
  `IsCommMonObj` witnesses are exactly those furnished by the dependency theorem.
  The simple index type is `base.support`; finite simple roots need no extra
  enumeration by Fin r. The background quotient Q=G/B does not occur in any of
  these group-point identities and therefore needs no extra presentation binder.
- The Weyl group is literally `RankOneRoots.Weyl iT`, namely the existing
  rational normalizer quotient by T(F). `act`, `hact` specify its conjugation
  action on the actual torus. `s : base.support → Weyl iT`, with `hs`, is exactly
  the simple root reflection: its action on every character is D.reflection.
  No generating, length-dichotomy, Bruhat-product or Coxeter-system assumption
  is added. `n` and `hn : ∀ w, QuotientGroup.mk (n w) = w` are the chosen lifts
  of bruhat_longest_cell_charts; they may be any such representatives.
- Every algebraically closed extension K/F is `(K : Type u) [Field K]
  [Algebra F K] [IsAlgClosed K]`. This follows the same scheme/field universe
  convention as the recorded Bruhat statement. No characteristic assumption occurs.
- D_w(K) is `simpleBruhatDoubleCoset iT iB (n w) (affine F K)`, definitionally
  `DoubleCoset.doubleCoset (toUnit _ ≫ (n w).val) (pointImage iB _) (pointImage iB _)`.
  Mathlib defines this as `B * {n_w} * B`; its membership is precisely the two
  B-factor formula. `open scoped Pointwise` uses the actual subset product.
- The first conjunction, quantified over every simple α and every w, states
  `length (s α * w) = length w + 1 ∨ length (s α * w) + 1 = length w`, then
  the increasing-case implication with the equality D_s D_w = D_sw, then
  the decreasing-case implication with the equality D_s D_w = D_sw ∪ D_w.
  Writing decrease as `length(sw)+1=length(w)` is equivalent to the intended
  integer decrement and avoids the erroneous truncated-natural reading at w=1.
  The two disjuncts cannot both hold in ℕ.
- For each `l : List base.support`, `l ≠ []` states nonemptiness, and
  `l.length = simpleBruhatWordLength s (l.map s).prod` states reducedness.
  The conclusion is exactly the ordered list product of the D_(s_i) equal to
  D_w, with w the ordered group product `(l.map s).prod`. Lists preserve order.
- The last conjunct is `simpleBruhatDoubleCoset ... (n 1) ... = pointImage iB ...`:
  D_1(K)=B(K). The empty list represents 1 by Mathlib List.prod; the empty-word
  convention is this final conjunct, not the empty product {1} of all subsets.

Dependency declarations read and used:

- `def-weil-field`: `Field`, Mathlib.Algebra.Field.Defs (class and docstring read).
- `def-weil-algebraic-closure`: `IsAlgClosed` from Mathlib.FieldTheory.IsAlgClosed.Basic;
  the dependency's match also records AlgebraicClosure and IsAlgClosure; no chosen
  algebraic closure is required for the two fields in this statement.
- `def-sc-group-scheme`: `CategoryTheory.GrpObj` and `CategoryTheory.Grp` from
  Mathlib.CategoryTheory.Monoidal.Grp, together with the actual kernel `GrpObj.ker`
  and homomorphism `IsMonHom` documented in WeilConjectures.AlgebraicGeometry.GroupScheme.Defs.
- `lem-sfb-reductive-borel-pair-structure`:
  Sheaf.AlgebraicGeometry.GroupScheme.ReductiveBorelPairStructure,
  `AlgebraicGeometry.reductive_borel_pair_structure` and
  `AlgebraicGeometry.semisimpleGroupScheme_isReductive`. The datum, root-base and
  conjugation/pairing binders are its output, not separately invented data.
- `lem-sfb-bruhat-longest-cell-charts`:
  Sheaf.AlgebraicGeometry.GroupScheme.BruhatLongestCellCharts,
  `AlgebraicGeometry.bruhat_longest_cell_charts`; its output representatives use
  exactly the quotient-map condition hn above. Its public RankOneRootInterfaces
  gives `Weyl`, `normalizer`, `pointImage`, and actual character Hom groups.
- `lem-sfb-reductive-rank-one-reflections`:
  Sheaf.AlgebraicGeometry.GroupScheme.ReductiveRankOneReflections,
  `AlgebraicGeometry.RankOneRoots.reductive_rankOne_reflections`; the simple
  reflections are specified by the same character action, expressed additively
  using the root datum furnished by the Borel-pair result.
- Stated proof-only dependencies are plain imports of
  Sheaf.AlgebraicGeometry.GroupScheme.ReductiveRootSubgroupParametrizations
  (`AlgebraicGeometry.TorusCharacterTangent.reductive_root_subgroup_parametrizations`)
  and Sheaf.AlgebraicGeometry.GroupScheme.BorelRootProductCoordinates
  (`AlgebraicGeometry.borel_root_product_coordinates`). The other four proof-only
  nodes have no recorded Lean declaration in the read snapshot, so no module was
  invented or imported for them. Their names remain in the full proof docstring.

Edge cases checked before writing: w=1 has only the increasing case. In rank one,
w=s gives D_s D_s = D_1 ∪ D_s. The reduced word of length one has exactly its
single double coset; repeated simple letters are not reduced. An empty word
represents 1 but its ambient subset-monoid product would be {1}, so it is excluded
from the nonempty clause and D_1=B is separate. Rank zero has no simple indices,
so only D_1=B remains. Characteristic two is allowed: the nonzero root parameter
1 and antidiagonal SL2 calculation still work. The choice of representative
n_1 in T need not be the identity. No irreducibility of the root system is assumed.
The minimum-length helper uses a Nat infimum; generation in this Weyl setting
ensures its defining set is nonempty, without adding generation as a hypothesis.

Searches made (2026-10-24):

- msearch.py leanfinder, "Multiplication of Borel double cosets by a simple reflection
  according to Weyl group word length": eight hits, CoxeterSystem.length_simple_mul,
  length_mul_simple, wordProd and related abstract Coxeter facts; none is the
  algebraic-group double-coset multiplication rule.
- msearch.py loogle, `"doubleCoset"`: twelve hits in DoubleCoset, including the
  existing doubleCoset, mem_doubleCoset and doubleCoset_eq_image2. Reused its
  actual definition instead of defining abstract double cosets again.
- msearch.py grep, `TitsSystem|BNPair|Bruhat|doubleCoset`, Mathlib/GroupTheory:
  five returned DoubleCoset hits; no BN/Tits multiplication theorem.
- msearch.py leansearch, "Multiplication rule for Borel Bruhat double cosets by a
  simple reflection": eight hits in DoubleCoset and CoxeterSystem.Length;
  none is this statement on Borel group-scheme points.
- msearch.py leanfinder, "Minimum length of a word in a specified family of
  generators of a group": FreeGroup.norm and CoxeterSystem.length, IsReduced,
  length_one, length_simple, length_wordProd_le, exists_reduced_word. These need
  a free group or a supplied CoxeterSystem, rather than this actual quotient
  with its specified simple reflections; no such extra structure is assumed here.
- rg in Mathlib/GroupTheory for wordLength, wordNorm and length definitions found
  CoxeterSystem.length only. Read that definition and DoubleCoset.doubleCoset.
- rg in lean/WeilConjectures and lean/Sheaf for Bruhat, doubleCoset,
  simple.*Length and wordLength found the existing Bruhat charts, Bott--Samelson
  consumer and abstract descent statements, but no duplicate theorem or helper.
  Read the full BottSamelsonGalleryGeometry interface as a concrete consumer check:
  its s, hs, act, hact, n and hn binders are identical, and its reducedness
  predicate is the same minimum-list-length condition. It explicitly cites this
  lemma in its proof plan and does not provide it.
- rg for this node's id in lean/WeilConjectures and for the new full-name suffixes
  simpleBruhatWordLength, simpleBruhatDoubleCoset and simple_bruhat_double_coset_product
  in Mathlib, WeilConjectures, Sheaf and dag/lean_names_upstream.json found no match.

Read the current blueprint unit from literature/blueprint/latest, the local Milne
PDF at printed pp.447--448 (PDF pp.459--460), and the three dependency modules in
full. The source's omitted final w in the T3 proof is already repaired explicitly
in the accepted node's proof and in this theorem's docstring. No statement change,
new nodes, dependency repair, or STATEMENT-DISPUTED flag is needed.

Validation: scompile.py compiled the sandbox and library module cleanly (2.5 s
and 2.4 s respectively). Every universe is explicit and autoImplicit is false.
Only the theorem has a postponed proof. Final dry-run and push are recorded by
the prescribed delivery tool.


## Second reading by Q50

(Written by the maintainer's independent reader, replacing the delivered
self-check, which stated it was not an independent reading.)

The node's statement as a list, with the Lean rendering and verdict:

1. F algebraically closed field: `{F : Type u} [Field F] [IsAlgClosed F]`. OK.
2. G semisimple: `hG : IsSemisimpleGroupScheme G.X` (owner def-sfb-semisimple-group-scheme,
   reached through the stmt_dep lem-sfb-reductive-borel-pair-structure, whose own
   stmt_deps list it); its body is smooth, connected, affine, finite type and no
   nontrivial smooth connected solvable normal closed subgroup. OK.
3. G simply connected: `hsc`, every surjective hom f : G' → G from a semisimple G'
   with finite kernel central on all A-points (all commutative F-algebras A in
   universe u = "after every scalar extension") is an iso. Same binder as the
   landed sibling `bottSamelson_gallery_geometry`. OK.
4. Split maximal torus T ⊆ B ⊆ G, B Borel: `iT, hT, hsplit, iB, hB, j, hj` verbatim
   the hypotheses of the second clause of `reductive_borel_pair_structure`. OK.
5. Roots Φ, positive roots, simple roots from the Borel-pair lemma: `Φ, D, base,
   hred, hroot, hpair, hΦ, hpos, aG, aB, haG, haB` and the two Prop-valued
   `IsCommMonObj` instances, exactly the existential output of that lemma; simple
   roots = `base.support`. OK.
6. W = N_G(T)(F)/T(F): `RankOneRoots.Weyl iT` (actual normalizer quotient,
   def-sfb-rank-one-root-interfaces). Representatives n_w: `n, hn` as in the
   output of `bruhat_longest_cell_charts` (any lifts; the double cosets do not
   depend on the lift since lifts differ by T(F) ⊆ B(K)). OK.
7. s_i = s_{α_i} of the rank-one reflections lemma: `act, hact` pin the
   conjugation action (same formula as the reflections and Bruhat-chart lemmas),
   `s, hs` pin s α by its character action x ↦ x − ⟨x,α∨⟩α, the same formula
   `x / α^{pairing x (coroot α)}` as `reductive_rankOne_reflections`. W acts
   faithfully on X(T), so s α is the reflection. OK.
8. ℓ(w) = least number of simple reflections with product w:
   `simpleBruhatWordLength s w = sInf {m | ∃ l, l.length = m ∧ (l.map s).prod = w}`,
   a real definition; the set is nonempty in this setting (simple generation),
   no generation hypothesis added. OK.
9. K/F algebraically closed extension, D_w(K) = B(K) n_w B(K):
   `K : Type u` (forced: K-points are maps from Spec K in Scheme.{u}),
   `simpleBruhatDoubleCoset iT iB (n w) (affine F K)` = Mathlib
   `doubleCoset (n_w) B(K) B(K)` = `B(K) * {n_w} * B(K)` with
   `pointImage iB` the image of B(K) in G(K). Subset products are the Pointwise
   `Set` monoid. OK.
10. Increasing case ℓ(s_i w) = ℓ(w)+1 ⇒ D_{s_i} D_w = D_{s_i w}; decreasing case
    ℓ(s_i w) = ℓ(w)−1 ⇒ D_{s_i} D_w = D_{s_i w} ∪ D_w (written ℓ(sw)+1 = ℓ(w),
    no truncated subtraction); "only two cases" is the disjunction. Quantified
    over every simple α and every w. OK.
11. Nonempty reduced word ⇒ ordered product of D_{s_{i_k}} = D_w: `l ≠ []`,
    `l.length = simpleBruhatWordLength s (l.map s).prod`, ordered list products. OK.
12. Empty word ↦ 1 and D_1(K) = B(K): separate last conjunct, with `n 1` any lift
    of 1. OK.

Edge cases: w = 1 (only the increasing case, D_s D_1 = D_s); rank one with
w = s (D_s D_s = D_1 ∪ D_s, the decreasing case); rank zero (no simple index,
only D_1 = B remains, and `n 1` ∈ T(F)); characteristic 2 or any p (no
characteristic hypothesis); length-one words. All covered.

Searches: rg in lean/Sheaf and lean/WeilConjectures of the side-live clone for
Bruhat, doubleCoset, WordLength/wordLength, and GroupScheme defs named
*length*/*coset*/*cell*/*word*: only BruhatLongestCellCharts and
BottSamelsonGalleryGeometry (which writes reducedness inline, no helper def),
no duplicate of either helper; Mathlib CoxeterSystem.length needs a Coxeter
system and DoubleCoset.doubleCoset is reused. The live node has no lean record yet.

Records: node changed only in `lean`; `lean.statement` is verbatim the file
signature; declarations list the two helpers and the theorem, all with source
and blueprint docstrings; the theorem's docstring carries the node's seven proof
steps; one `sorry`, no proof beyond it.

No mismatch in the Lean or the records was found; this section replaces the
self-check only.
