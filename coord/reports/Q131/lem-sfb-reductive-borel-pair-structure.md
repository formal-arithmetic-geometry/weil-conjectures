## Worker report

Item: `lem-sfb-reductive-borel-pair-structure`.
Module: `Sheaf.AlgebraicGeometry.GroupScheme.ReductiveBorelPairStructure`.
Declarations: `AlgebraicGeometry.reductive_borel_pair_structure` and
`AlgebraicGeometry.semisimpleGroupScheme_isReductive`. Both proofs are `sorry`.
There are no new definitions, axioms, new nodes, or dependency-module repairs.
The mathematical statement, proof, and proof dependencies of the item are unchanged.
The statement dependencies gain seven already landed definition nodes, as permitted
by brief-stage2 §5 (STMT_DEPS MAY GAIN LANDED NODES).

I read the item's statement and all ten proof steps, its five original statement
dependencies and their records, and the declarations and docstrings used below.
The old CompactObject example is a withdrawn empty module; I also read its recorded
replacement `WeilConjectures.CategoryTheory.CompactObject` for the actual example.
No repair note for this item was present.

Source checked directly in the local Milne PDF (pdftotext in the sandbox):
16.33(a)--(d), printed pp.335--336; 17.6--17.12, pp.353--355;
19.22 and following paragraph, p.402; 21.11--21.12, pp.428--430;
21.29--21.35, pp.433--435; Section 18c, p.390. These give respectively
the unipotent radical and torus complement, Borel quotients and existence,
splitting, the reduced integral root datum, the Borel positive system,
and the actual B-torsor. Sections 19a--19b and 14.21 give the final implication.

### Hypothesis and clause correspondence

1. An algebraically closed field F is `{F : Type u} [Field F] [IsAlgClosed F]`.
   These are the recorded Mathlib notions on def-weil-field and
   def-weil-algebraic-closure, not private field predicates. The universe is explicit.
2. An F-group scheme is `G : Grp (Over (Spec (.of F)))`: its underlying object
   `G.X` has exactly the recorded `CategoryTheory.GrpObj` structure. Homomorphisms
   such as `iT`, `iB`, `j`, `iU` and `p` are bundled group-object morphisms, hence
   already satisfy `IsMonHom` on their underlying maps.
3. Reductivity is `hG : ReductiveTorusCentralizer.IsReductive G`, the existing
   affine finite-type smooth geometrically connected predicate excluding smooth
   connected normal unipotent subgroups over the algebraic closure. Since F is
   algebraically closed, F → AlgebraicClosure F is an isomorphism, so this is
   precisely the absolute convention of the item, without an extra hypothesis.
   `SolvableGroupStructure.IsUnipotent` uses a faithful closed immersion into GL_n
   and unipotent matrices on every algebraically closed extension; it includes
   smoothness. The same predicate is used for the radical and all its competitors.
4. The first conjunct gives `∃ T B iT iB`, with
   `ReductiveTorusCentralizer.IsMaximalTorus iT`, the existing torus definition,
   `∃ r, Nonempty (T ≅ MultiplicativeType.splitTorus F r)` for splitting over F,
   `IsBorelGroupScheme iB.hom.hom`, and `∃ j, j ≫ iB = iT` for containment.
   Maximality is scheme-theoretic, not maximality of F-points. Borel solvability
   is the recorded terminating scheme-theoretic commutator series. The split
   torus is an actual product of the recorded Laurent-coordinate G_m.
5. The second conjunct universally quantifies over every T, B, their inclusions,
   and every containment homomorphism j satisfying that same square. Thus all
   later assertions hold for each such pair, not just the chosen one.
6. The quotient clause is `∃ (Q : Over (Spec (.of F))) (π : G.X ⟶ Q)`.
   `IsProper Q.hom`, `LocallyOfFiniteType Q.hom` and `QuasiCompact Q.hom` are
   exactly properness and finite type of its structure morphism. The explicit
   finite-type conjuncts mirror the item's explicit finite-type clause.
7. Faithfully flat means `Flat π.left ∧ Surjective π.left` as in the node.
   With `m = fst G.X B.X * (snd G.X B.X ≫ iB.hom.hom)`, the equation
   `m ≫ π = fst G.X B.X ≫ π` is π(gb)=π(g). The following
   `IsPullback (fst G.X B.X) m π π` says precisely that the canonical map
   `(g,b) ↦ (g,gb)` identifies G ×_F B with G ×_Q G. This specifies the right
   multiplication comparison itself, rather than an arbitrary isomorphism.
   Products and pullback squares in Over use the actual fibre products of
   schemes over the named base. Faithful flatness and this kernel pair
   characterize the represented quotient sheaf G/B. No quotient of F-points
   is substituted. The equivariance equation is written explicitly because
   the node explicitly asks for it, even though a pullback square includes it.
8. The radical clause provides a group scheme U with closed normal inclusion
   `iU : U ⟶ B`, smoothness, connectedness and the existing unipotence predicate.
   For every other smooth connected normal unipotent closed subgroup `iN`,
   `∃ f, f ≫ iU = iN` expresses largestness. This pins U to R_u(B), up to the
   unique subgroup identification; U is not an arbitrary unipotent subgroup.
9. The projection `p : B ⟶ T` is a group-scheme homomorphism by its bundled type.
   `j ≫ p = 𝟙 T` is identity on T. The square
   `IsPullback iU.hom.hom (toUnit U.X) p.hom.hom η[T.X]` identifies its
   scheme-theoretic kernel with the given U, respecting its inclusion.
   The map in `IsIso ((fst U.X T.X ≫ iU.hom.hom) *
   (snd U.X T.X ≫ j.hom.hom))` is exactly multiplication U ×_F T → B.
   Together with normality, this is the assertion B=U⋊T: the semidirect law
   follows by multiplication and conjugation inside B. It is not an assertion
   that the direct-product group law makes this map a homomorphism.
10. The lattices are literally
    `Additive (T ⟶ Grp.mk (StandardGroupSchemes.multiplicative F))` and
    `Additive (Grp.mk (StandardGroupSchemes.multiplicative F) ⟶ T)`.
    Additive changes multiplicative notation for the actual Hom groups;
    it does not replace them by unrelated free modules. Two existential
    `IsCommMonObj` witnesses expose commutativity of T and G_m so Lean can
    form these additive Hom groups. They are conclusions, not assumptions
    on G or the chosen pair, and do not change the underlying group laws.
    `Module.Finite ℤ` on both groups supplies finite generation. Perfect
    integer pairing then also implies their freeness, as documented on
    Mathlib's `RootDatum`; no separate, arbitrarily chosen lattice is used.
11. `Φ` is a Finset of these actual characters. `P : RootDatum Φ X X_*`
    is Mathlib's perfectly paired integral root datum, with finite index Φ.
    `(∀ α : Φ, P.root α = α.val)` fixes its root embedding to that character
    set. The condition on every character is
    `χ ∈ Φ ↔ χ ≠ 0 ∧ weightSpace T G χ.toMul ≠ ⊥`.
    Thus it is exactly all nonzero Lie weights, without added or missing roots.
12. The actual actions `aG : ModObj T.X G.X` and `aB : ModObj T.X B.X` are
    fixed to `(iT.hom.hom ⊗ₘ 𝟙 G.X) ≫ GrpObj.conj G.X` and
    `(j.hom.hom ⊗ₘ 𝟙 B.X) ≫ GrpObj.conj B.X`, respectively. The weights
    use the recorded `TorusCharacterTangent.weightSpace` with these explicit
    actions. That definition tests the true character values on dual-number
    tangent points in `GrpObj.Lie`; it does not differentiate the character.
    No arbitrary action or characteristic-zero Lie algebra is substituted.
13. For every actual character χ and cocharacter ν, the pairing normalization is
    `ν.toMul.hom.hom ≫ χ.toMul.hom.hom = (𝟙 G_m) ^ (P.toLinearMap χ ν)`.
    Powers here are powers of scheme morphisms into a group object. On every
    algebra this is t ↦ t^〈χ,ν〉, including negative exponents. Thus the
    perfect pairing in P is exactly the canonical integer composition pairing.
14. `P.IsReduced` gives reducedness; crystallographic integrality is built into
    a pairing over ℤ (Mathlib's self-valued instance supplies IsCrystallographic).
    The coroot embedding, root-coroot pairing 2 and the simultaneous reflection
    permutations are fields of RootPairing. In particular `reflectionPerm_root`
    is exactly x-〈x,α∨〉α on roots. No root-spanning hypothesis is imposed.
15. `b : P.Base` gives the simple-root base, integral independence and the
    same-sign integral expansions of every root, as well as the compatible
    coroot base. `b.IsPos α ↔ weightSpace T B α.val.toMul ≠ ⊥` fixes the
    positive system precisely to the roots in Lie(B). Mathlib's Base already
    describes positive and negative integral simple-root expansions; its
    IsPos uses positive height. Thus no unrelated positive system is chosen.
16. The final sentence of the node is a separate declaration,
    `semisimpleGroupScheme_isReductive`, with only IsSemisimpleGroupScheme G.X
    as hypothesis and IsReductive G as conclusion. The recorded semisimple
    predicate is exactly smooth connected affine finite type with no nontrivial
    smooth connected solvable normal subgroup. This implication is not placed
    under a reductivity hypothesis and is therefore not vacuous.

### Recorded dependencies and imports

Original statement dependencies: Field (Mathlib.Algebra.Field.Defs), IsAlgClosed
(Mathlib.FieldTheory.IsAlgClosed.Basic, publicly available through the imports),
GrpObj, Grp, IsMonHom and the subgroup predicates in
WeilConjectures.AlgebraicGeometry.GroupScheme.Defs; and IsProper, Flat, Surjective,
LocallyOfFiniteType and QuasiCompact for def-pc-morphism-conventions. That last
node is expressly a convention, so it has no module/declaration of its own.

The added, already landed definition nodes are:

- def-sfb-borel-subgroup-scheme: Sheaf.AlgebraicGeometry.GroupScheme.Borel,
  AlgebraicGeometry.IsBorelGroupScheme.
- def-sfb-semisimple-group-scheme: Sheaf.AlgebraicGeometry.GroupScheme.Semisimple,
  AlgebraicGeometry.IsSemisimpleGroupScheme and IsSolvableGroupScheme.
- def-sfb-reductive-torus-centralizer-terminology:
  Sheaf.AlgebraicGeometry.ReductiveTorusCentralizerTerminology,
  AlgebraicGeometry.ReductiveTorusCentralizer.IsReductive and IsMaximalTorus.
- def-sfb-solvable-group-structure: Sheaf.AlgebraicGeometry.SolvableGroupStructure,
  AlgebraicGeometry.SolvableGroupStructure.IsUnipotent and IsAlgebraic.
- def-sfb-tori-multiplicative-type: Sheaf.AlgebraicGeometry.ToriMultiplicativeType,
  AlgebraicGeometry.MultiplicativeType.IsTorus and splitTorus.
- def-sfb-torus-character-tangent-weights:
  Sheaf.AlgebraicGeometry.TorusCharacterTangentWeights,
  AlgebraicGeometry.TorusCharacterTangent.weightSpace.
- def-sc-gm-ga: Sheaf.AlgebraicGeometry.StandardGroupSchemes,
  AlgebraicGeometry.StandardGroupSchemes.multiplicative and multiplicativeGroup.

The public imports expose these existing notions, transitively where appropriate.
Mathlib.LinearAlgebra.RootSystem.Base and Reduced expose RootDatum, Base and
IsReduced. Mathlib.AlgebraicGeometry.Morphisms.Proper exposes IsProper.
Proof-only imports are PerfectSolvableUnipotentTorus for
AlgebraicGeometry.perfect_solvable_unipotent_torus, RootSystem.BaseExists for
RootPairing.linearIndepOn_root_baseOf', and RingTheory.Bialgebra.MonoidAlgebra
for AddMonoidAlgebra.isGroupLikeElem_iff_mem_range_single_one. I read their
signatures and source. The other proof dependencies have no recorded Lean yet
in the read clone, so no nonexistent module is imported. None is required to
state the item, and no downstream theorem is used to define any object here.

### Edge cases

G=1 permits rank zero, B=T=U=1, Q=Spec F and Φ empty. There is no Nonempty
hypothesis on Φ; P.Base may have empty support. If G is any torus, B=T=G,
U=1 and Q=Spec F, while the full nonzero-rank character and cocharacter lattices
remain even though Φ is empty. This checks that no IsRootSystem/spanning
assumption slipped into the root datum. For SL₂ in characteristic two, the root
character can have zero differential, but is still nontrivial as a character;
weights here use its actual values, so those roots remain. Scheme-theoretic
closed and normal inclusions, the kernel square and the torsor square retain
nonreduced test algebras. The empty scheme cannot be a group scheme over a field
because it would have no identity section; no artificial Nonempty assumption
is required. Negative pairings use integer powers, not natural powers.
The semisimple implication includes the trivial semisimple group and uses no
characteristic-zero assumption.

### Searches actually run

- msearch.py leanfinder: "Borel pairs of a reductive algebraic group maximal
  split torus proper quotient root datum". Eight hits: RootPairing.EmbeddedG2,
  RootPairing.GeckConstruction.h', RootPairing.nonempty_base, the EmbeddedG2
  index-set lemma, and four measurable Borel-space quotient instances. None
  states a Borel-pair theorem for group schemes.
- msearch.py loogle: "RootDatum, IsReductive, BorelSubgroup". Zero hits;
  returned diagnostic: unknown identifier IsReductive. This is not recorded
  as an unavailable service or as evidence against the project predicates.
- msearch.py grep: "IsReductive|BorelSubgroup|IsUnipotent|RootDatum". Two
  Mathlib hits in LinearAlgebra/RootSystem/Defs.lean (documentation line 25
  and RootDatum line 109). I read RootPairing and RootDatum in full, and
  Base, Reduced and IsValuedIn; these supply the abstract root datum, not
  its realization on the characters of an algebraic group.
- rg in lean/WeilConjectures and lean/Sheaf for Borel, IsReductive,
  IsUnipotent, IsSplitTorus, IsSemisimple, RootDatum and rootPairing found
  the reusable project definitions listed above and no matching theorem.
  The exact node-id search in WeilConjectures found no existing declaration.
  The full new declaration names were checked in both trees and in
  dag/lean_names_upstream.json; no collision was found.
- The current live reductive-terminology source was also read with
  scompile.py --source; it agrees with the local source.

### Validation

scompile.py compiled the delivered module cleanly on 2026-10-24, both its
sandbox form (30.1 s) and its named library form (12.2 s). No errors or
unexpected warnings. The file explicitly disables autoImplicit, declares u,
and has no line longer than 100 characters. Only the two named theorem
proofs contain sorry. No statement correction or STATEMENT-DISPUTED flag is
needed. deliver2.py --no-push passed preflight and compilation, reporting
OK (dry run) at commit 21db7c57126; no files were pushed by the dry run.

## Second reading by Q131

This is the author's second pass under the direct-dispatch brief, not a claim
of independent review; the maintainer performs the independent reading.
I reopened the node and the complete Lean module after successful compilation.
The review focused on the easy-to-miss semantic points: the universal clause
covers every split pair; the torsor is for RIGHT multiplication and fixes the
comparison map; p is a homomorphism on B, is identity on the GIVEN T and has
the GIVEN radical as its scheme kernel; multiplication is only required to
be an isomorphism of underlying schemes, as appropriate for a semidirect
product. The actual Hom lattices, composition-normalized pairing,
conjugation-normalized actions, equality of Φ with all nonzero weights, and
identification of b.IsPos with the Borel weights are all present. The root
set can be empty without forcing either lattice to vanish. Semisimple implies
reductive is a separate theorem with no prior reductivity hypothesis.

No mathematical mismatch was found and no source statement was changed.
The initial type probe showed that the existing G_m interface does not expose
its commutativity as an inferred instance; the delivered conclusion explicitly
provides the commutativity witnesses needed to form the Hom lattices. This
adds no hypothesis and never changes the existing G_m or torus group laws.
No helper definition, arbitrary map, chosen unpinned object, or proof was
introduced to get the statement to elaborate.
