## Worker report

The module `Sheaf.AlgebraicGeometry.GroupScheme.CentralIsogenyBorelRootCompatibility`
states `AlgebraicGeometry.centralIsogeny_borel_root_compatibility` and
`AlgebraicGeometry.splitTorus_semisimple_borel_root_compatibility`. Both proofs are
`sorry`; there are no new definitions, axioms, instances, or helper theorems.
The node changes only in `lean`. There is no statement correction or disputed clause.

The first theorem renders the central-isogeny assertion. Its data and hypotheses match
as follows.

| Node hypothesis or notion | Lean rendering |
| --- | --- |
| Algebraically closed field F | `{F : Type u} [Field F] [IsAlgClosed F]` |
| F-group schemes G and H | `G H : Grp (Over (Spec (.of F)))` |
| G reductive | `hG : ReductiveTorusCentralizer.IsReductive G` |
| H affine and of finite type | `hH : SolvableGroupStructure.IsAlgebraic H`; this unfolds to affineness, locally finite type and quasi-compactness |
| H smooth and connected | `hHs : Smooth H.X.hom`, `hHc : ConnectedSpace H.X.left` |
| Group homomorphism q | `q : H ⟶ G` in the category of group objects |
| Faithful flatness on coordinate algebras | `hq : q.hom.hom.left.appTop.hom.FaithfullyFlat`; the existing `RingHom.FaithfullyFlat` is precisely faithful flatness of the induced scalar-extension module |
| Scheme-theoretic kernel K | `GrpObj.ker q.hom.hom`, the existing fibre product with the target identity |
| Finite kernel | `hK : IsFinite (GrpObj.ker q.hom.hom).hom`; over a field this is equivalently a finite-dimensional coordinate algebra |
| Central kernel after every scalar extension | `hcentral` quantifies over every F-scheme A and every kernel point x and H-point g, and says their products commute. Testing all schemes is equivalent to testing all affine scalar extensions by the sheaf property |
| Every Borel pair (B,T) of G | Universal binders `T B iT iB`, the existing `IsMaximalTorus iT`, a split-torus isomorphism witness of rank r, `IsBorelGroupScheme iB.hom.hom`, and `j : T ⟶ B` with `j ≫ iB = iT` |

The conclusions match as follows.

| Node clause | Lean rendering |
| --- | --- |
| H is reductive | First conjunct `ReductiveTorusCentralizer.IsReductive H` |
| There is a lifted Borel pair | Existentials `TH BH iTH iBH jH` with maximal-torus, splitness and Borel predicates and `jH ≫ iBH = iTH` |
| Scheme-theoretic inverse images of T and B | `IsPullback iTH.hom.hom qT.hom.hom q.hom.hom iT.hom.hom` and the corresponding `IsPullback` for BH, qB and iB; these specify precisely the inverse-image subgroups with their restriction maps |
| K is contained in TH | `kT : Grp.mk (GrpObj.ker q.hom.hom) ⟶ TH` and `kT.hom.hom ≫ iTH.hom.hom = GrpObj.kerι q.hom.hom`. Since both subgroup embeddings are monic, this is actual inclusion |
| The two restrictions are faithfully flat | `qT.hom.hom.left.appTop.hom.FaithfullyFlat` and the identical predicate for qB |
| The unipotent radicals as in the dependency | U and UH are closed, normal, smooth connected unipotent subgroup schemes of B and BH, with the universal containment property for all such subgroups. Unipotence is the existing `SolvableGroupStructure.IsUnipotent`, defined by a faithful matrix representation and geometric unipotence |
| The projections as in the dependency | `p : B ⟶ T` and `pH : BH ⟶ TH`, identity on the given torus (`j ≫ p = 𝟙 T`, and likewise), with U and UH their scheme-theoretic kernels and U × T → B multiplication isomorphisms. These conditions specify the canonical semidirect-product projections |
| The radicals map isomorphically | `qU : UH ⟶ U`, `IsIso qU`, and `qU ≫ iU = iUH ≫ qB`; combined with the BH inverse-image square this is the restriction of q |
| The projections commute with q | `qB ≫ p = pH ≫ qT` |
| Character and cocharacter lattices | Actual additive Hom groups `Additive (T ⟶ Grp.mk (StandardGroupSchemes.multiplicative F))` and `Additive (Grp.mk (StandardGroupSchemes.multiplicative F) ⟶ T)`, and likewise for TH |
| The roots and coroots of the dependency | Root data P and PH with finite integral lattices and reducedness. Their root maps are the actual character inclusions; their pairings are pinned by composition of characters and cocharacters as integer power maps; their root sets are precisely the nonzero tangent character weights under the actual conjugation action |
| Positive and simple roots of the given Borel | Bases b and bH with positivity exactly the tangent weight criterion for B and BH. `b.support` and `bH.support` are the simple-root sets |
| Pullback identifies roots | `e : Φ ≃ ΦH`, with `(PH.root (e α)).toMul = qT ≫ (P.root α).toMul` |
| Corresponding coroots | `(PH.coroot (e α)).toMul ≫ qT = (P.coroot α).toMul`, explicitly rendering the corresponding-coroot assertion used in the node proof |
| Positive and simple roots correspond | `bH.IsPos (e α) ↔ b.IsPos α` and `e α ∈ bH.support ↔ α ∈ b.support` |
| All character-coroot pairings agree | The final universal equation quantifies over every character χ, not just roots: `PH.toLinearMap (Additive.ofMul (qT ≫ χ.toMul)) (PH.coroot (e α)) = P.toLinearMap χ (P.coroot α)` |

The second theorem renders the final product clause independently of the chosen
central-isogeny presentation, so it applies to the lifted pair obtained in the first
theorem. It quantifies over Z, S and every split Borel pair TH ⊆ BH of Z ⊗ S.
This is the same product assertion: one can also take q to be the identity to obtain
any such pair from the main setup. The hypothesis `hZ` says Z is a split torus,
including rank zero; `hS : IsSemisimpleGroupScheme S.X` is the existing semisimplicity
predicate. `TH`, `BH`, `iTH`, `iBH`, `jH`, `hTH`, `hTHs`, `hBH`, `hjH` specify the pair.
The conclusion gives TS ⊆ BS in S with the same maximal/split/Borel/incidence properties.
The equalities
`eT.hom ≫ (𝟙 Z ⊗ₘ iTS) = iTH` and
`eB.hom ≫ (𝟙 Z ⊗ₘ iBS) = iBH`
for isomorphisms eT and eB mean exactly TH = Z × TS and BH = Z × BS as subgroup
schemes of the product, not merely abstract isomorphisms of groups.
Both product root data have the same character, pairing, conjugation and tangent-weight
specifications as above. The equivalence `e : ΦS ≃ ΦH` identifies each root with its
pullback along `eT.hom ≫ snd Z TS`. Coroots, after eT, equal
`lift (0 : Grp.mk (StandardGroupSchemes.multiplicative F) ⟶ Z) (PS.coroot α).toMul`.
Here the categorical zero is the trivial group homomorphism, hence this is exactly
(1, α∨) in multiplicative notation. Positive and simple roots correspond as well.

The auxiliary specifications of root data and radicals repeat the *conditions* on
the actual objects from the dependency, not new definitions of those objects. In
particular actions and pairings are never arbitrary unconstrained parameters. The
existential commutativity witnesses allow the actual Hom groups to carry their
additive commutative group structures, just as in the dependency's declaration.

Dependencies read and used:

- `Mathlib.Algebra.Field.Defs`: `Field`.
- `Mathlib.FieldTheory.IsAlgClosed.Basic`: `IsAlgClosed`; the recorded algebraic-closure
  dependency also points to `AlgebraicClosure` and `IsAlgClosure`, which were read.
  The assertion uses an already algebraically closed F, so no new closure is chosen.
- `Mathlib.CategoryTheory.Monoidal.Grp`: `CategoryTheory.GrpObj`, `Grp`, `Grp.Hom`,
  tensor products and Cartesian products of group objects.
- `WeilConjectures.AlgebraicGeometry.GroupScheme.Defs`: the concrete group-scheme
  specialization, closed/normal subgroup predicates and finite-kernel terminology;
  `GrpObj.ker` and `GrpObj.kerι` are defined in
  `WeilConjectures.Mathlib.CategoryTheory.Monoidal.Cartesian.Grp`.
- `Sheaf.AlgebraicGeometry.GroupScheme.ReductiveBorelPairStructure`:
  `AlgebraicGeometry.reductive_borel_pair_structure` and
  `AlgebraicGeometry.semisimpleGroupScheme_isReductive`. Read the full signatures,
  docstrings and the imported `IsReductive`, `IsMaximalTorus`, `IsUnipotent`,
  `IsAlgebraic`, `IsBorelGroupScheme`, `IsSemisimpleGroupScheme`, and
  `TorusCharacterTangent.weightSpace` definitions. The statement uses these notions
  directly, with no replacement terminology.
- `Mathlib.RingTheory.RingHom.FaithfullyFlat`: `RingHom.FaithfullyFlat`.
- `Mathlib.LinearAlgebra.RootSystem.Base` and `Reduced`: `RootDatum`, its pairing,
  roots and coroots, `RootPairing.Base`, `Base.IsPos` and `Base.support`.

The plain proof imports cover the currently stated proof dependencies:
`AffineHomomorphismFlatImage`, `ReductiveTorusSelfCentralizer`,
`ReductiveRankOneReflections`, the upstream geometric reducedness and Nullstellensatz
modules, and `Mathlib.RingTheory.Artinian.Module` for `IsArtinianRing.equivPi`.
Closed immersion is already a public transitive import of the statement dependency.
The remaining proof nodes (unipotent quotient images, quotient Borel/torus images,
split-torus subgroups, multiplicative-isogeny Borel comparison, isogeny root-power
laws and root-product coordinates) have no recorded Lean declaration at this base;
no speculative module import was added. They are proof-only prerequisites, not
missing notions needed to state this item. The nine proof steps, including their
DAG lemma names, appear in the two theorem docstrings.

Edge cases checked before writing:

- q = identity: inverse-image pairs and restrictions are identities; the kernel is
  trivial and all equations have the expected identity specialization.
- Pure tori and the trivial group: Φ and ΦH may be empty. There is no nonemptiness
  condition on either root set or simple base; the equivalence and pairing clauses
  are vacuous. The unipotent radicals are trivial, and projections remain included.
- Positive characteristic and μ_p kernel: no kernel smoothness, reducedness,
  separability or prime-to-characteristic condition is assumed. All centrality and
  inverse-image clauses retain scheme structure, and root weights are characters,
  not differentials. The torus Frobenius is included with empty root systems.
- The central isogeny SL₂ → PGL₂: pullback can have nontrivial cokernel on character
  lattices; the statement requires only a bijection of roots, never a lattice
  isomorphism. The pairing equation is for arbitrary target characters.
- Product with Z of rank zero, or S trivial: the product assertion includes both;
  it permits empty root systems and the categorical zero/trivial Z-coroot component.
- Universes: F and schemes use the existing common universe u; no independent
  smaller universe of test algebras is introduced. Centrality is tested on all
  schemes in this universe, including every affine F-algebra in the same size.

Searches for an existing statement (all via the prescribed search wrapper or
read-only rg):

1. `leanfinder`: “A central isogeny of reductive algebraic groups identifies Borel
   pairs roots coroots unipotent radicals”. Eight hits, concerning abstract root
   pairings or characteristic-zero Lie theory; none is the group-scheme assertion.
2. `loogle`: `RootDatum, IsBorelGroupScheme, IsReductive`. Zero hits; unknown
   Mathlib identifier `IsBorelGroupScheme` (this is a project definition).
3. Mathlib `grep`: `central.isogeny|IsBorelGroupScheme|IsReductive`. Zero hits.
4. `leansearch`: “central isogeny reductive algebraic group Borel maximal torus root
   datum”. Eight hits; `RootDatum` is useful terminology, the others concern Lie
   algebras or abstract centres, with no exact result.
5. `rg` in `lean/WeilConjectures` and `lean/Sheaf`, including the exact item id and
   `central.isogeny|CentralIsogeny`, found only the different semisimple
   central-isogeny-multiplicative theorem. Read it: its conclusion is faithful
   flatness and a diagonalizable kernel, not Borel/root compatibility.
6. Searches for the proposed declaration names in Mathlib, both project trees and
   `dag/lean_names_upstream.json` found no existing declarations.

Source checked directly in `literature/milne-algebraic-groups_iAG2017.pdf`, printed
pp.391 and 483–486 (PDF pp.403 and 495–498), via pdftotext: proof of 18.18 gives
inverse-image Borel and quotient compatibility; 23.1–23.2 specify the root/coroot
maps of central isogenies; 23.4 preserves positive/simple systems; 23.5 is the
induced root-data theorem and centrality criterion. No modification of the source
statement was necessary.

Validation: `scompile.py NZ lem-sfb-central-isogeny-borel-root-compatibility` compiled
the delivered file both as its sandbox module (7.1 s) and as its actual library
module (5.8 s), with no errors and no warnings. An initial compiler pass caught
Lean's reserved λ binder, a product group-instance elaboration issue (resolved by
explicitly supplying the product's existing `.grp` instance to the Borel predicate),
and multiplicative notation for the trivial bundled hom (corrected to categorical
zero). None changed the mathematical assertion. All binders and universe variables
are explicit and `set_option autoImplicit false` is enabled.

## Second reading by NZ

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
