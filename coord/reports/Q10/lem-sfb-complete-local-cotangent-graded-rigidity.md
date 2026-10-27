## Worker report

The module `Sheaf.RingTheory.CompleteLocalCotangentGradedRigidity` states
`IsLocalRing.surjective_and_isomorphism_of_cotangent_surjective_of_complete`.
Its sole theorem has proof `sorry`. No definitions or other nodes are introduced.
The item changes only in `lean`; its statement, dependencies and proof remain unchanged.
There is no repair note and no statement dispute.

I read Stacks `formal-defos.tex`, Tag 06GZ, label
`lemma-surjective-cotangent-space`, statement and proof (lines 868–910), and
`artin.tex`, Tag 07XH, label `lemma-approximate-versal`, including the argument
following the dotted-arrow diagram (lines 1874–1932). The node extracts the
absolute cotangent criterion and the equal-graded-dimension argument; its accepted
proof replaces the inverse-system passage by Nakayama and the complete-source
surjectivity lemma. The theorem docstring gives all six proof steps and their
DAG dependencies, including the kernel induction for injectivity.

Hypotheses and clauses, matched individually:

| Node | Lean rendering |
| --- | --- |
| Commutative rings C and D | `(C : Type u) (D : Type v)`, `[CommRing C] [CommRing D]` |
| Noetherian | `[IsNoetherianRing C] [IsNoetherianRing D]` |
| Unique maximal ideals m and n | `[IsLocalRing C] [IsLocalRing D]`, with `maximalIdeal C` and `maximalIdeal D` |
| Complete for these maximal ideals | `[IsAdicComplete (maximalIdeal C) C]` and the D instance |
| Common field k | `(k : Type w) [Field k]` |
| Fixed residue-field identifications | `(eC : ResidueField C ≃+* k) (eD : ResidueField D ≃+* k)` |
| Ring map f | `(f : C →+* D)` |
| Locality, f⁻¹(n) = m | `[IsLocalHom f]`; `IsLocalRing.maximalIdeal_comap f` gives precisely this equality |
| Induced residue map is the identity under the identifications | `hres : eD.toRingHom.comp (ResidueField.map f) = eC.toRingHom` |
| Surjective canonical cotangent map | `hcot : Function.Surjective (Ideal.mapCotangent ... f.toIntAlgHom (maximalIdeal_comap f).symm.le)` |
| f is surjective | First conjunct `Function.Surjective f` |
| Every j ≥ 0 | `∀ j : ℕ`, including zero |
| Graded pieces m^j/m^(j+1), n^j/n^(j+1) | The explicitly displayed quotients of the ideals `maximalIdeal C ^ j` and `maximalIdeal D ^ j` by `maximalIdeal C • ⊤` and `maximalIdeal D • ⊤` inside those ideals |
| Their specified k-vector-space structures | Natural quotient-ring module action, then `@Module.compHom (C ⧸ maximalIdeal C) k ... eC.symm.toRingHom`, and the corresponding D action |
| Equality of dimensions | Equality of the two explicitly instantiated `@Module.finrank k` expressions |
| Conditional isomorphism of the given map f | Implication from the dimension equality to `∃ e : C ≃+* D, e.toRingHom = f` |

Two presentation details were checked against the actual definitions. First,
`Ideal.mapCotangent` is used with integer scalars, so it applies to an arbitrary
ring homomorphism without introducing a coefficient-field embedding. Its formula
`Ideal.mapCotangent_toCotangent` is `[c] ↦ [f(c)]`. This underlying function is
exactly the function of the k-linear cotangent map: if a coefficient in k is
represented by a in C, residue compatibility says its image is represented by
f(a) in D, and f(ac) = f(a)f(c). Surjectivity is independent of which linear
presentation bundles that same function.

Second, for `M = (m^j : Ideal C)`, `m • (⊤ : Submodule C M)` consists exactly of
finite sums of products a*x with a in m and x in m^j. Its image in C is
m*m^j = m^(j+1); hence the displayed quotient is the actual graded piece, with
its actual induced residue-field action, not a surrogate dimension invariant.
`Module.Quotient.mk_smul_mk` gives the action on representatives. `Module.compHom`
restricts this action along eC.symm and so transports it to k. No ring map k → C
or k → D is assumed. Noetherianity implies m^j is finitely generated; its quotient
is finite over C and over C/m (the instance near Torsion/Basic.lean:729), hence
finite-dimensional over k after transport. Thus `Module.finrank` really is the
cardinality of a finite basis in every degree; its convention for infinite rank
never intervenes. There is no additional finite-dimensionality hypothesis.

Dependency declarations read and used:

- `def-weil-pbc-noetherian-ring`: `Mathlib.RingTheory.Noetherian.Defs`,
  `IsNoetherianRing` (line 196) and `isNoetherianRing_iff_ideal_fg`: every ideal
  finitely generated, exactly the node.
- `def-weil-pbc-adic-completion`: `Mathlib.RingTheory.AdicCompletion.Basic`,
  `AdicCompletion` (line 171) and `IsAdicComplete` (line 56). The first is compatible
  quotient sequences; the second combines Hausdorffness and precompleteness,
  equivalently bijectivity of the completion map as recorded by the dependency.
- `def-weil-field`: Mathlib `Field`, `Mathlib.Algebra.Field.Defs`, line 180.
- `lem-weil-pbc-nakayama-jacobson`: proof import `Mathlib.RingTheory.Nakayama`,
  `Submodule.eq_bot_of_le_smul_of_le_jacobson_bot`, lines 118–120.
- `lem-weil-pbc-complete-source-surjective-mod-ideal`: proof import
  `Mathlib.RingTheory.AdicCompletion.Functoriality`,
  `surjective_of_mk_map_comp_surjective`, lines 447–450.
- `lem-trf-vector-space-quotient-dimension`: proof import
  `Mathlib.LinearAlgebra.Dimension.RankNullity`,
  `Submodule.finrank_quotient_add_finrank`, lines 248–252.
- `lem-trf-finite-dimensional-short-exact-dimension`: proof import
  `Mathlib.Algebra.Category.ModuleCat.Free`,
  `ModuleCat.free_shortExact_finrank_add`, lines 181–190.

Supporting Mathlib interfaces read: `IsLocalRing`, `local_hom_TFAE`,
`maximalIdeal_comap`, `ResidueField.map`, `Ideal.Cotangent`, `Ideal.mapCotangent`,
`Module.isTorsionBySet_quotient_ideal_smul`, the quotient-ring module instance,
`Module.Quotient.mk_smul_mk`, `Module.compHom` and `Module.finrank`.
All statement imports are public and proof-only imports are plain imports.
All variables and universes are explicit, with `set_option autoImplicit false`.

Edge cases checked mathematically:

- j = 0: m^0 is the whole ring and its quotient by m is the residue field, of
  k-dimension one. The quantifier has no positive-degree restriction.
- Fields: m = n = 0; the cotangent map is between zero spaces. Identity of the
  residue-field identifications makes f an isomorphism; all positive graded
  dimensions are zero.
- Mixed characteristic: Z_p → F_p is allowed by the signature and is surjective;
  its graded dimensions disagree in degree one, so the second assertion does
  not apply. No k-algebra structure excludes this example.
- k[[t]] → k[[t]]/(t²): surjectivity and the cotangent hypothesis hold, but graded
  dimensions first disagree in degree two. This checks the need for all degrees.
- The zero ring has no field residue and is excluded by the source's local-ring
  and residue-field hypotheses, just as by `IsLocalRing` and the equivalences.
- u, v and w are independent; neither equal ring universes nor a coefficient-field
  lift is required.

Searches actually run using `batch2/msearch.py` (the sandbox search log records
queries, results and dates):

- LeanFinder: “A local homomorphism of complete noetherian local rings is surjective
  if its residue field map and cotangent map are surjective, and is bijective if
  all associated graded dimensions agree”. Eight hits, including
  `RingHom.SurjectiveOnStalks.residueFieldMap_bijective` and
  `surjective_of_isLocalization_isMaximal`; none states this theorem.
- Loogle: `IsLocalRing.CotangentSpace, Ideal.quotient, AssociatedGraded`.
  Zero hits with diagnostic `unknown identifier 'Ideal.quotient'`; this malformed
  identifier query does not establish absence of a theorem.
- Mathlib grep: `cotangentMap|mapCotangent|gradedPiece|surjective.*cotangent|cotangent.*surjective`
  in RingTheory. Twenty-five reported hits, including the existing canonical
  `Ideal.mapCotangent` interface and AdicCompletion.LocalRing; no exact theorem.
- LeanSearch: “A local homomorphism between complete Noetherian local rings with
  identical residue fields is surjective when its map on cotangent spaces is
  surjective”. Eight hits: residue surjectivity, `ResidueField.map`,
  `local_hom_TFAE`, relative extension cotangent results and local properties;
  none is the absolute complete-local rigidity theorem.
- `rg` in the project `lean/WeilConjectures` and `lean/Sheaf`, and the upstream
  name index, for cotangent, associated graded, maximal-ideal powers and the
  proposed declaration name. Also searched the item id with `grep -rn` in
  `lean/WeilConjectures` (no match). Existing graded pieces belong to
  `Ideal.associatedGradedPiece`; no second definition is introduced here: the
  theorem displays the ordinary Mathlib quotient by m*M directly. I opened
  `Sheaf.RingTheory.CompleteLocalCotangentSurjectivity`; its theorem is a relative
  cotangent criterion for complete local k-algebras with a coefficient algebra,
  so it does not cover this node's arbitrary mixed-characteristic rings or
  its conditional isomorphism conclusion.

Validation: `scompile.py Q10 lem-sfb-complete-local-cotangent-graded-rigidity`
compiled the delivered file cleanly against the live server library (3.4 seconds
for the library module). A preceding module-mode scalar-transport probe checked
the explicit quotient module and `Module.compHom` elaboration. The final file
contains no diagnostic commands and no proof other than the prescribed `sorry`.

## Second reading by Q10

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
