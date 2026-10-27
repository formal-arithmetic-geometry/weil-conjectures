## Worker report

The module Sheaf.AlgebraicGeometry.GroupScheme.SchubertClosureCellGeometry states
AlgebraicGeometry.Schubert.schubert_closure_cell_geometry. Its only theorem has proof
`by sorry`; four real helper definitions unpack notions explicitly introduced by this node:
`wordLength` is the infimum of simple-word lengths, `SubwordLE` is the reduced-subword
relation, `reducedClosure` uses Mathlib's vanishingIdeal and subscheme, and `conjugateLie`
is the span of the actual conjugated Lie(B) tangent points. No new independent notion,
new node, dependency repair, or statement correction is needed.

Hypotheses, one by one:

- F, Field F, IsAlgClosed F give the algebraically closed field, with arbitrary universe u.
- G, T, B are Grp objects over Spec F. hG is the existing IsSemisimpleGroupScheme:
  smooth, connected, affine, finite type, and no smooth connected solvable normal subgroup.
- hsc is precisely the stated simply connected condition: every surjective semisimple
  cover with finite kernel, central on every commutative algebra, is an isomorphism.
- iT, hT, hsplit are the split maximal torus; iB, hB are the Borel inclusion;
  j, hj express T contained in B. The commutativity instances express the torus group laws.
- aG, aB, haG, haB specify the actual conjugation actions. Φ, D, base, hred, hroot,
  hpair, hΦ, hpos unpack exactly the root datum and positive simple base supplied by
  reductive_borel_pair_structure; no separate abstract root system is substituted.
- Q, π, hQ, hπflat, hπsurj, hπinv, hπtorsor unpack the proper finite-type flag quotient
  and faithfully flat right B-torsor of that same recorded dependency.
- RankOneRoots.Weyl iT is the actual N_G(T)(F)/T(F). act, hact pin its action by
  conjugation. s, hs pin the simple reflections by their root reflection formula.
- n, hn specify representatives. w₀, hw₀ specify reversal of the positive roots.
  These parameters express the fixed choices in the node, rather than added restrictions.

Conclusions, clause by clause:

- The first existential-list clause gives generation of every w by the s. wordLength
  is then the least possible length; empty words are allowed.
- The next three universal clauses give reflexivity, transitivity and antisymmetry.
  The following equivalence quantifies over EVERY reduced b for w, so the relation is
  independent of a chosen reduced expression. The next implication gives strict length
  increase for x <= w, x != w.
- wordLength s w₀ = Nat.card {α : Φ // base.IsPos α} is ℓ(w₀)=N.
- C, Cminus, c, cminus give immersed (locally closed) smooth schemes. The two Over
  isomorphisms identify them with A^{ℓ(w)} and A^{N-ℓ(w)} over F, not merely as schemes.
- The two geometric-point equivalences identify these schemes with B n_w B/B and
  (n₀ B n₀^{-1}) n_w B/B over every algebraically closed extension K/F. Thus no
  arbitrary affine stratification can satisfy the statement in place of Bruhat cells.
- The two exists-unique range clauses partition the full underlying scheme space Q.
  Together with local closedness and finiteness of the recorded Weyl group these are
  the finite stratifications. This also supplies disjointness in both closure unions.
- IsOpenImmersion (cminus 1).left and DenseRange give the open dense opposite identity cell.
- reducedClosure explicitly selects the reduced induced structure. The two IsIntegral
  clauses and two topologicalKrullDim equalities give integrality and the two dimensions.
- The two closure range equalities, indexed by SubwordLE s x w and SubwordLE s w x,
  are exactly the ordinary and opposite closure formulas. Because the families partition
  Q these unions are disjoint unions. The final two IsOpen clauses in the closure subtype
  topology express that each cell is open in its own closure.
- E identifies Lie(G)/Ad(n_w)Lie(B) with the recorded schemeTangentSpace at e_w.
  It is an additive equivalence plus an explicit scalar law along the canonical map
  F -> κ(e_w), hence precisely an F-linear equivalence without a new scalar instance.
  Its next formula fixes E to the actual derivative g -> g n_w B: tangentPoint v is
  right-multiplied by the constant n_w and composed with π, then the dual-number
  coefficients are transported by the canonical structural residue map.
- The two following equivalences characterize membership of a tangent vector in each
  cell by factorization of its dual-number morphism through that cell's immersion.
  The corresponding quotient submodules are the sums of the existing character weight
  spaces with base.IsPos α (respectively its negation), excluding the image wΦ+.
  They are exactly Φ+ minus wΦ+ and (-Φ+) minus wΦ+. IsCompl asserts complementarity.
  These use torus-character weights, never differentials of characters.

Dependency declarations read and reused:

- Mathlib: Field (Algebra.Field.Defs), IsAlgClosed (FieldTheory.IsAlgClosed.Basic),
  CategoryTheory.GrpObj (CategoryTheory.Monoidal.Grp), AffineSpace (AlgebraicGeometry.
  AffineSpace), Scheme.IdealSheafData.vanishingIdeal (AlgebraicGeometry.IdealSheaf.Basic).
- Sheaf.AlgebraicGeometry.GroupScheme.ReductiveBorelPairStructure:
  reductive_borel_pair_structure, semisimpleGroupScheme_isReductive, with its public
  IsSemisimpleGroupScheme, IsBorelGroupScheme, IsMaximalTorus terminology.
- Sheaf.AlgebraicGeometry.GroupScheme.ReductiveRankOneReflections:
  RankOneRoots.reductive_rankOne_reflections; its public RankOneRootInterfaces gives
  Character, Weyl, normalizer and pointImage. Full declaration and docstrings inspected.
- Sheaf.AlgebraicGeometry.GroupScheme.BruhatLongestCellCharts:
  bruhat_longest_cell_charts, including its quotient, conjugation action and representatives.
- WeilConjectures.AlgebraicGeometry.SchemeTangentSpace: schemeTangentSpace and its canonical
  additive and residue-field module structures. Its recorded differential and docstring
  were read; factorization on the actual dual-number morphisms avoids scalar transport
  choices for the cell inclusions.
- Existing TorusCharacterTangent.weightSpace and GrpObj.tangentPoint are used directly.

Proof imports include the already recorded BorelRootProductCoordinates,
ReductiveRootSubgroupParametrizations, BottSamelsonGalleryGeometry,
WeilConjectures.AlgebraicGeometry.ReducedInducedClosedSubscheme and DenseCompactification,
and Mathlib polynomial dimension. Proof-only nodes with no recorded module at reading
(weyl-reflection-realization, simple-root-reflection-generation, root-sign-word-deletion,
flag-torus-fixed-geometry, projective-attracting-cells, simple-bruhat-double-coset-product,
solvable-proper-fixed-point, longest-subword-order-duality) cannot yet be imported; their
proof uses remain in the ten-step theorem docstring. Proper/finiteness permanence is
already transitively available through the geometric imports.

Edge cases checked: empty Φ and simple base give the trivial Weyl group and Q=A⁰, the
empty word has length zero, both cells and closures have dimension zero, and the two
zero quotient subspaces are complementary in zero. In rank one the identity cell has
ordinary dimension zero and opposite dimension one, with roles reversed at w₀.
No characteristic or positive-rank assumption appears. IsPos and its negation partition
roots, so negative roots are included even in characteristic two. The use of ULift (Fin n)
keeps affine spaces in Scheme.{u}. The geometric-point quantifiers use Type u, matching
F and the schemes; all generic scheme points have residue fields at that size.

Searches actually run (2026-10-24):

- msearch leanfinder: "Schubert closure Bruhat subword order affine cells tangent root spaces";
  eight root-system/Lie-weight hits, no flag-scheme closure theorem.
- msearch loogle: "CoxeterSystem, List.Sublist"; zero hits.
- msearch grep: "Schubert|Bruhat|schemeTangent" in AlgebraicGeometry; zero hits.
- msearch leansearch: "Schubert variety closure Bruhat cells complementary tangent spaces";
  eight analytic tangent-cone/cotangent/CW-complex hits, none this statement.
- rg in lean/WeilConjectures and lean/Sheaf for Schubert, Bruhat, subword; found the
  recorded Bruhat charts and abstract strong-exchange extension, not this result.
  Literal item-id grep of WeilConjectures found nothing.
- Mathlib group-theory search for wordLength/wordNorm found no corresponding definition;
  project search found no prior reduced-subword relation for this Weyl quotient.
  Reduced closure reuses the existing Mathlib construction rather than recreating it.

Source: Milne primary local PDF pp.446--449 read with pdftotext, particularly 21.70--21.79
and the tangent quotient at the normalizer flags. The node records the Brion--Kumar
closure/subword source; the linked author-hosted PDF fetch timed out. No source-based
statement change was made. No STATEMENT-DISPUTED or node fault found.

Validation: scompile.py compiled the sandbox and actual module against the published live
library cleanly (approximately four seconds per file). All variables/universes are bound;
there are no diagnostic commands, file-local notation, hollow definitions or proved theorems.


## Second reading by Q42

Independent second reading by the maintainer's reviewer, in place of the delivery's
same-worker self-check. Statement read clause by clause against the node, the Lean records of
lem-sfb-reductive-borel-pair-structure, lem-sfb-reductive-rank-one-reflections and
lem-sfb-bruhat-longest-cell-charts, Mathlib RootPairing.Base.IsPos, schemeTangentSpace and
TorusCharacterTangent.weightSpace.

Objects and hypotheses:
- F algebraically closed, universe u: `[Field F] [IsAlgClosed F]`. OK.
- G semisimple simply connected: `hG : IsSemisimpleGroupScheme G.X` and `hsc`, identical to the
  landed `simplyConnected_character_lattice` encoding (surjective, finite kernel, kernel central on
  all F-algebras ⇒ IsIso). OK.
- Split maximal torus T ⊆ Borel B: iT/hT/hsplit/iB/hB/j/hj verbatim from the Borel-pair lemma. OK.
- Φ, Φ⁺, simple roots: Φ/D/base/hred/hroot/hpair/hΦ/hpos verbatim from the Borel-pair output;
  IsPos ↔ weight space in Lie(B) nonzero, so ¬IsPos is exactly -Φ⁺. Root datum pinned by T. OK.
- Q = G/B: Q/π/hQ/hπflat/hπsurj/hπinv/hπtorsor verbatim from the Borel-pair output. OK.
- W = N_G(T)(F)/T(F) = RankOneRoots.Weyl iT; act pinned by hact (conjugation), so
  (act w).inv ≫ χ = w·χ with (wχ)(t)=χ(n⁻¹tn) as in the Bruhat-chart node. OK.
- Simple reflections s: pinned by hs as D.reflection at each simple root; unique since W acts
  faithfully on X(T). OK.
- n_w arbitrary representatives (hn); w₀ pinned by hw₀ (Φ⁺ ↦ -Φ⁺; unique by the chart lemma). OK.
- B⁻ = n₀Bn₀⁻¹, e_w = n_wB: rendered in the point clauses and the tangent base point. OK.

Conclusion:
- generation by simple reflections; ℓ = wordLength (sInf of word lengths, real data). OK.
- ≤ = SubwordLE (reduced a sublist of reduced b); reflexive, transitive, antisymmetric; independence
  of the reduced expression b (∀ reduced b); x<w ⇒ ℓ(x)<ℓ(w); ℓ(w₀)=N. OK.
- cells: immersions (locally closed), smooth, ≅ A^{ℓ(w)} resp. A^{N-ℓ(w)} over F; pinned as
  B n_w B/B and B⁻ n_w B/B on K-points for every algebraically closed K/F; partition of all of
  |Q| by each family; together with immersion + smooth source this fixes the reduced structure. OK.
- C⁻₁ open immersion with dense range. OK.
- reducedClosure = Mathlib vanishingIdeal subscheme of the closure (real reduced-induced
  structure); IsIntegral; topologicalKrullDim = ℓ(w), N-ℓ(w); closure(C_w) = ⋃_{x≤w} C_x,
  closure(C⁻_w) = ⋃_{x≥w} C⁻_x (disjoint by the partition); each cell open in its closure. OK.
- tangent: E : Lie(G)/Ad(n_w)Lie(B) ≃+ T_{e_w}Q with scalar law along F → κ(e_w) (F-linear),
  pinned on every v by the orbit derivative (1+εv)·n_w ↦ π; conjugateLie = Ad(n_w)Lie(B) via
  tangent points. Cell tangent subspaces = dual-number factorizations through the immersions;
  they equal the images of ⊕ g_α over Φ⁺∖wΦ⁺ resp. (-Φ⁺)∖wΦ⁺ (α ∉ {wβ : β>0}); IsCompl. Checked
  against T_{e_w}Q ≅ ⊕_{Φ∖wΦ⁺} g_α: directions and dimensions ℓ(w), N-ℓ(w) agree. OK.

Edge cases: r=N=0 (empty base.support, W trivial, wordLength 0, zero tangent quotient, IsCompl ⊥ ⊥);
rank one (C₁ point, C⁻₁ = A¹); every characteristic (torus-character weights, ¬IsPos covers
negatives). Universes: single u throughout; AffineSpace on ULift.{u} (Fin n). No extra assumptions.

Helpers wordLength, SubwordLE, reducedClosure, conjugateLie are real data with source/blueprint
docstrings. Parallel unlanded Q50 delivery defines `simpleBruhatWordLength` (proof_dep only,
different namespace, no clash): advisory. GrpObj.Lie / tangentPoint (blueprint sk-d-tangent) are
reached through def-sfb-rank-one-root-interfaces → def-sfb-torus-character-tangent-weights → sk-d-tangent,
as for the landed root-group items. lean.statement equals the file signature verbatim; one `sorry`.
No mismatch found.
