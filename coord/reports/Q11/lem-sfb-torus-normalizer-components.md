## Worker report

The module `Sheaf.AlgebraicGeometry.GroupScheme.TorusNormalizerComponents` states
`AlgebraicGeometry.torus_normalizer_centralizer_components`. Its sole proof is `sorry`.
There are no new definitions, dependency repairs, new nodes, or statement corrections.
Only the item's `lean` record changes.

Source read: Milne, Algebraic Groups (2017), Corollary 12.40, printed p.244,
and Corollaries 13.10 and 13.11, printed p.257. The local PDF text explicitly
identifies the identity components scheme-theoretically and deduces normalizer
smoothness from centralizer smoothness. The finite-component argument is the
node's sixth proof step. The module docstring records all six accepted proof
steps and their cited node IDs. The two proof dependencies not yet recorded in
Lean, `lem-sfb-torus-centralizer-smooth-connected` and
`lem-sfb-diagonalizable-hom-family-rigidity`, are named in the proof plan;
they introduce no object required to type this statement.

Hypotheses and clauses, matched to Lean:

- An algebraically closed field F: `(F : Type u) [Field F] [IsAlgClosed F]`.
- Group schemes over F: `(G S : Grp (Over (Spec (.of F))))`. These are bundled
  group objects with actual group laws, not arbitrary pointwise group structures.
- Affine finite-type G: `[IsAffine G.X.left] [LocallyOfFiniteType G.X.hom]
  [QuasiCompact G.X.hom]`. The two latter classes are the recorded definition
  of finite type. S's affineness and finite type follow from its displayed
  isomorphism to a finite product of G_m; they need not be additional assumptions.
- Smooth and connected G: `[Smooth G.X.hom] [ConnectedSpace G.X.left]`.
- Closed subgroup S in G: `(i : S ⟶ G) [IsClosedSubgroupScheme i.hom.hom]`.
  Bundling the homomorphism in `Grp` retains compatibility with multiplication.
- Any torus, including rank zero: `hS : ∃ r : ℕ, Nonempty
  (S ≅ MultiplicativeType.splitTorus F r)`. This is exactly the splitting
  stated by this node, using the existing product of the existing G_m.
  No maximality or reductivity is assumed; those words in the introductory
  terminology citation impose no hypothesis on this node.
- Representing normalizer and centralizer: existential group schemes `N C`
  and inclusions `iN iC`, both `IsClosedSubgroupScheme`, affine, locally of
  finite type and quasi-compact, with `Smooth N.X.hom ∧ Smooth C.X.hom`.
  Existential finite-type instances are introduced before identity components.
- N(A) is the displayed normalizer functor: the range of composition with iN
  equals the set of g such that, for every F-algebra map `f : A →ₐ[F] B`,
  conjugation by `StandardGroupSchemes.map F f ≫ g` sends the image of S(B)
  onto itself. This is equality, not one-sided containment. It quantifies over
  every commutative algebra B, including nonreduced algebras. Every A-algebra
  extension is equivalently such an F-algebra map with the induced structure.
- C(A) is the recorded scheme-theoretic centralizer: the range of composition
  with iC equals `ReductiveTorusCentralizer.centralizerPoints i A`, which
  already tests commutation after every algebra extension. No private copy.
- Equality of identity components as subgroup schemes of G: an isomorphism
  `e : GrpObj.identityComponent N.X ≅ GrpObj.identityComponent C.X` whose
  composition with C's inclusion into G equals N's inclusion into G. The
  recorded identity-component construction uses the open subscheme structure,
  not a reduced structure or only the underlying connected point set. Equality
  over G also forces the isomorphism to respect the inherited group operations.
- Finite quotient group N(F)/C(F): `j : C ⟶ N` with `j ≫ iN = iC` and
  `IsNormalSubgroupScheme j.hom.hom`; the quotient of the group
  `(𝟙_ (Over (Spec (.of F))) ⟶ N.X)` by the range of
  `IsMonHom.monoidHom j.hom.hom (𝟙_ _)` is `Finite`. Normality is part of the
  asserted conclusion, so this is a quotient group, and the commuting triangle
  identifies its denominator with exactly C(F), rather than an arbitrary
  finite-index subgroup. The closed immersion iC makes j injective on points.

Dependency declarations read and used:

- `Field`, Mathlib.Algebra.Field.Defs; `IsAlgClosed`,
  Mathlib.FieldTheory.IsAlgClosed.Basic (accessed through the recorded imports).
  The arbitrary algebraically closed field is not specialized to a chosen
  `AlgebraicClosure` construction.
- `CategoryTheory.GrpObj` / `CategoryTheory.Grp`,
  Mathlib.CategoryTheory.Monoidal.Grp, via the bundled group-scheme imports.
- `AlgebraicGeometry.IsClosedSubgroupScheme` and
  `AlgebraicGeometry.IsNormalSubgroupScheme`,
  WeilConjectures.AlgebraicGeometry.GroupScheme.Defs. Their signatures explicitly
  require a group homomorphism and test injectivity/normality over every algebra.
- `AlgebraicGeometry.LocallyOfFiniteType` and `QuasiCompact`,
  Mathlib.AlgebraicGeometry.Morphisms.FiniteType and QuasiCompact; `Smooth`,
  Mathlib.AlgebraicGeometry.Morphisms.Smooth; `ConnectedSpace`,
  Mathlib.Topology.Connected.Basic.
- `AlgebraicGeometry.ReductiveTorusCentralizer.centralizerPoints`,
  Sheaf.AlgebraicGeometry.ReductiveTorusCentralizerTerminology.
- `AlgebraicGeometry.MultiplicativeType.splitTorus`,
  Sheaf.AlgebraicGeometry.ToriMultiplicativeType, supplied by the terminology
  dependency's public import chain. Its recursion starts at the trivial group
  and uses the recorded `StandardGroupSchemes.multiplicative` at each step.
- `StandardGroupSchemes.affine`, `map`, `multiplicative`,
  Sheaf.AlgebraicGeometry.StandardGroupSchemes (def-sc-gm-ga), through that chain.
- `GrpObj.identityComponent` and `GrpObj.identityComponentι`,
  WeilConjectures.AlgebraicGeometry.GroupScheme.Basic. These are the full open
  subscheme and its inclusion, with the finite-type binders used here.

Proof imports include the recorded ConstantSourceClosedFactorizationLocus and
GroupNeutralComponentTranslates modules. The other stated proof inputs are
Mathlib closed immersions, pullbacks, separatedness, open immersion lifts and
smooth restriction/locality, imported explicitly or available through the public
Basic/Smooth imports. No import is made for the two unstated proof dependencies.

Edge cases checked before drafting: r=0 gives S=1 and N=C=G, hence trivial
quotient; G itself a torus gives N=C=G; a nonmaximal torus is admitted; the
standard diagonal torus in SL2 has quotient of order two, also in characteristic
two (no division by two or characteristic restriction occurs). Nonreduced A and
B are admitted by both point conditions, including the zero algebra. G cannot
be the empty scheme because a group object has its identity section. The
universe of test algebras is the same `u` as F and the schemes, so the tests
include their coordinate algebras and are not vacuous size-restricted tests.

Searches actually run (2026-10-24):

1. msearch.py leanfinder: "A torus in a smooth connected affine algebraic group
   has smooth normalizer and centralizer with equal identity components and
   finite quotient". Eight hits, including `Subgroup.normal_centralizer`,
   topological and Lie-algebra results; no group-scheme theorem matching this node.
2. msearch.py loogle: "Subgroup.normalizer, Subgroup.centralizer". Twelve hits,
   including centralizer containment/normality in an abstract group normalizer;
   none supplies representability, smoothness or scheme identity components.
3. msearch.py grep: `normalizer.*[Tt]orus|[Tt]orus.*normalizer|centralizer.*identityComponent`.
   Zero Mathlib hits.
4. msearch.py leansearch: "normalizer centralizer torus group scheme smooth
   same connected component". Eight hits on abstract subgroup normalizers,
   centralizers and Sylow theory; no match for the theorem.
5. rg of WeilConjectures for normalizer/centralizer and the exact node ID:
   Hopf-ideal/monodromy normalizer statements only, no theorem matching the node.
6. rg of lean/Sheaf for normalizer/centralizer, including GroupScheme modules:
   `RankOneRoots.normalizer` treats only rational points, the Cartan normalizer
   result assumes a smooth subgroup containing a maximal-torus centralizer,
   and the self-centralizer result assumes a reductive group and maximal torus.
   None states this theorem for an arbitrary torus in an arbitrary smooth
   connected affine group. Reused the exact existing general centralizer-points
   definition and split-torus definition. Checked the cocharacter-specific
   centralizer too; it is less general than the recorded terminology dependency.
7. Read the recorded dependency signatures and docstrings, the example module
   (now withdrawn), its replacement node record, and searched the upstream name
   inventory by the group-scheme IDs. No duplicate theorem name was found.

No STATEMENT-DISPUTED flag or node fault is warranted. No source correction
or new mathematical notion is needed. All variables are explicitly bound and
`autoImplicit` is false. Lines have at most 100 characters.

## Second reading by Q11

Second reading done by the maintainer's independent reviewer (cc review service, 2026-10-24).
It replaces the worker's own self-check, which was in this section before. Read: the item node,
the nine stmt_deps and their Lean records, Milne iAG2017 Cor. 12.40, 13.10 and 13.11 as cited,
the module `Sheaf/AlgebraicGeometry/GroupScheme/TorusNormalizerComponents.lean`, and the
declarations it uses in the live tree.

Node clauses and the Lean that renders each:

1. F algebraically closed field: `(F : Type u) [Field F] [IsAlgClosed F]`. Any algebraically
   closed field, not only a chosen `AlgebraicClosure`. Correct.
2. G and S affine group schemes over F: `G S : Grp (Over (Spec (.of F)))`, bundled group objects
   (def-sc-group-scheme `GrpObj`). Correct.
3. G affine of finite type, smooth and connected: `[IsAffine G.X.left] [LocallyOfFiniteType
   G.X.hom] [QuasiCompact G.X.hom] [Smooth G.X.hom] [ConnectedSpace G.X.left]`. These are the
   recorded declarations of def-weil-finite-type-morphism, def-sbc-smooth-morphisms and
   def-weil-connected-scheme. Correct.
4. S ⊆ G a closed subgroup: `(i : S ⟶ G) [IsClosedSubgroupScheme i.hom.hom]`. This is the
   def-sc-group-scheme-subgroup class: injective on all R-points and a closed immersion. Correct.
5. S a torus, meaning isomorphic to G_m^r for some r ≥ 0: `∃ r : ℕ, Nonempty (S ≅
   MultiplicativeType.splitTorus F r)`. `splitTorus` is defined by recursion: `𝟙_` for r = 0, and
   for r + 1 the product `Grp.mk (StandardGroupSchemes.multiplicative F) ⊗ splitTorus F r`. So it
   is the r-fold product of the def-sc-gm-ga G_m, and r = 0 is allowed. No maximality or
   reductivity is assumed. Correct.
6. N_G(S) represented by a closed subgroup scheme: `∃ N iN`, `IsClosedSubgroupScheme iN.hom.hom`,
   and for every F-algebra A (Type u), `range (· ≫ iN) = {g | ∀ B (f : A →ₐ[F] B), conj by g_B
   maps i(S(B)) onto i(S(B))}`. This is equality of sets of B-points for every A-algebra B,
   including nonreduced B. That is exactly the node's "preserves S_{A'} as a subgroup functor"
   (proof step 1 reads it as equality gS_Ag⁻¹ = S_A). Correct.
7. C_G(S) represented: `range (· ≫ iC) = ReductiveTorusCentralizer.centralizerPoints i A`. This is
   the recorded terminology-node definition: commutes with every point of S after every
   extension. Correct.
8. Both smooth and of finite type: affine for N and C, existential `LocallyOfFiniteType`/
   `QuasiCompact` instances, `Smooth N.X.hom ∧ Smooth C.X.hom`. Correct.
9. N° = C°: an iso `e : GrpObj.identityComponent N.X ≅ GrpObj.identityComponent C.X` over F, with
   `e.hom ≫ ι_C ≫ iC = ι_N ≫ iN`. The upstream `identityComponent` is the open subscheme on the
   connected component of the identity, so the structure is not reduced. The composites into G
   are monomorphisms, so this is equality as subschemes of G. Correct.
10. N(F)/C(F) finite: `j : C ⟶ N` with `j ≫ iN = iC`, `IsNormalSubgroupScheme j.hom.hom`, and
    `Finite` of the quotient of `𝟙_ ⟶ N.X` (the F-points) by the image of C(F). The commuting
    triangle pins the denominator to C(F). Normality on all R-points is proved by node step 6,
    which works for every A, so asserting it is not stronger than what the node establishes.
    Correct.

Edge cases. For r = 0, S is trivial, N = C = G and the quotient is trivial. If G is a torus, the
quotient is trivial. For the diagonal torus of SL2 the quotient has order 2 in every
characteristic. No characteristic hypothesis appears. The test algebras live in the universe u of
F, so the coordinate rings of S, G and their base changes are among the test algebras.

One definition per notion. `RankOneRoots.normalizer` (def-sfb-rank-one-root-interfaces) is a
subgroup of rational points only, not a representing scheme, so it is not a duplicate. A grep of
the live Sheaf and WeilConjectures trees for normalizer definitions found nothing else. No other
module states this theorem, and the module is not in the live tree.

Advisory notes, no change. `GrpObj.identityComponent` belongs to the existing:true record
def-wf-algebraic-components, which is not cited. The node's text gives the meaning of ∘ inline,
and other landings have accepted the same use. `splitTorus` belongs to def-sfb-tori-multiplicative-type,
which is reached through the cited def-sfb-reductive-torus-centralizer-terminology. Neither is
a mismatch.

Docstrings carry the source place, the blueprint id and the six proof steps. The proof is `sorry`.
No definitions were added. The lean record statement is identical to the file signature.
Mismatches found: none in the Lean. Changed: this section only.
